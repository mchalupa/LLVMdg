cmake_minimum_required(VERSION 3.1)

# FIXME: Unfortunately, C is (at least temporarily) required due to a bug in
# LLVM 14.  See https://github.com/llvm/llvm-project/issues/53950.
project(dg LANGUAGES C CXX)

include(CTest)

# we need at least C++17 standard
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

option(LLVM_DG "Support for LLVM Dependency graph" ON)
option(ENABLE_CFG "Add support for CFG edges to the graph" ON)
option(NO_EXCEPTIONS "Compile with -fno-exceptions (ON by default)" ON)

if(NOT CMAKE_BUILD_TYPE)
  message(STATUS "Build type not set. Setting default.")
  set(CMAKE_BUILD_TYPE
      "RelWithDebInfo"
      CACHE STRING "" FORCE)
endif()
message(STATUS "Build type: ${CMAKE_BUILD_TYPE}")
set_property(CACHE CMAKE_BUILD_TYPE PROPERTY STRINGS "Debug" "RelWithDebInfo"
                                             "MinSizeRel" "Release")

if(LLVM_DG)
  # for llvm dg we need cfg and postdom edges
  if(NOT ENABLE_CFG)
    message(STATUS "Enabling CFG edges due to llvm dg")
  endif()

  set(ENABLE_CFG ON)

  find_package(LLVM REQUIRED CONFIG)

  message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
  message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")
  message(STATUS "LLVM binaries: ${LLVM_TOOLS_BINARY_DIR}")

  set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${LLVM_DIR}")
  include(LLVMConfig)
  include(AddLLVM)

  message(STATUS "LLVM include dir: ${LLVM_INCLUDE_DIRS}")
  message(STATUS "LLVM libraries dir: ${LLVM_LIBRARY_DIRS}")
  message(STATUS "LLVM definitions: ${LLVM_DEFINITIONS}")

  # if we were provided a path to custom sources use that path
  if(LLVM_SRC_PATH)
    include_directories(SYSTEM ${LLVM_SRC_PATH}/include)
    message(STATUS "Looking for headers in given: ${LLVM_SRC_PATH}/include")
  else()
    include_directories(SYSTEM ${LLVM_INCLUDE_DIRS})
    message(STATUS "Looking for headers in: ${LLVM_INCLUDE_DIRS}")
  endif()

  # if we were provided a path to custom build directory use that
  if(LLVM_BUILD_PATH)
    link_directories(${LLVM_BUILD_PATH}/lib)

    # llvm-config.h
    include_directories(SYSTEM "${LLVM_BUILD_PATH}/include")
    message(STATUS "Looking for libraries in given: ${LLVM_BUILD_PATH}/lib")
  else()
    link_directories(${LLVM_LIBRARY_DIRS})
    message(STATUS "Looking for libraries in: ${LLVM_LIBRARY_DIRS}")
  endif(LLVM_BUILD_PATH)

  add_definitions(${LLVM_DEFINITIONS})

  option(LLVM_LINK_DYLIB "Link with LLVM dynamically" ON)

  if(LLVM_LINK_DYLIB)
    message(STATUS "LLVM linking: dynamic")
    if(${LLVM_PACKAGE_VERSION} VERSION_LESS "3.8")
      set(llvm LLVM-${LLVM_PACKAGE_VERSION})
    else()
      # only LLVM 3.8+ provide unversioned library
      set(llvm LLVM)
    endif()
  else()
    message(STATUS "LLVM linking: static")
    if(${LLVM_PACKAGE_VERSION} VERSION_GREATER "3.4")
      llvm_map_components_to_libnames(llvm_analysis analysis)
      llvm_map_components_to_libnames(llvm_irreader irreader)
      llvm_map_components_to_libnames(llvm_bitwriter bitwriter)
    else()
      llvm_map_components_to_libraries(llvm_irreader irreader)
      llvm_map_components_to_libraries(llvm_bitwriter bitwriter)
      llvm_map_components_to_libraries(llvm_analysis analysis)
    endif()
  endif()

  # LLVM 18 and newer require at least c++17 standard
  set(CMAKE_CXX_STANDARD 17)
  option(USE_CXX17 "Use C++17 standard" ON)
endif(LLVM_DG)

if(SVF_DIR)
  set(HAVE_SVF ON)
  add_definitions(-DHAVE_SVF)
  set(SVF_LIBDIR ${SVF_DIR}/lib)

  if(NOT SVF_INCLUDE)
    if(EXISTS "${SVF_DIR}/include/WPA/Andersen.h")
      set(SVF_INCLUDE ${SVF_DIR}/include)
    elseif(EXISTS "${SVF_DIR}/../include/WPA/Andersen.h")
      set(SVF_INCLUDE ${SVF_DIR}/../include)
    else()
      message(FATAL_ERROR "Did not find the directory with SVF headers")
    endif()
  endif()

  set(SVF_LIBS Svf Cudd)

  include_directories(SYSTEM ${SVF_INCLUDE})
  link_directories(${SVF_LIBDIR} ${SVF_LIBDIR}/CUDD)

  if(NOT LLVM_LINK_DYLIB)
    if(${LLVM_PACKAGE_VERSION} VERSION_GREATER "3.4")
      llvm_map_components_to_libnames(llvm_transformutils transformutils)
    else()
      llvm_map_components_to_libraries(llvm_transformutils transformutils)
    endif()
  endif()

  message(STATUS "SVF dir: ${SVF_DIR}")
  message(STATUS "SVF libraries dir: ${SVF_LIBDIR}")
  message(STATUS "SVF include dir: ${SVF_INCLUDE}")
  message(STATUS "SVF libs: ${SVF_LIBS}")
endif(SVF_DIR)

if(TSL_HOPSCOTCH_DIR)
  set(HOPSCOTCH_DIR ${TSL_HOPSCOTCH_DIR}/include/)
  if(NOT EXISTS "${HOPSCOTCH_DIR}/tsl/hopscotch_map.h")
    message(
      FATAL_ERROR "Tessil hopscotch map NOT FOUND in ${TSL_HOPSCOTCH_DIR}")
  endif()

  include_directories(SYSTEM ${HOPSCOTCH_DIR})
  message(STATUS "Found Tessil Hopscotch map in ${HOPSCOTCH_DIR}")
  message(STATUS "Adding include dir ${HOPSCOTCH_DIR}")
  add_definitions(-DHAVE_TSL_HOPSCOTCH)
endif()

if(ENABLE_CFG)
  add_definitions(-DENABLE_CFG)
endif()

message(STATUS "Using compiler: ${CMAKE_CXX_COMPILER}")

# --------------------------------------------------
# Fuzzing
# --------------------------------------------------
include(CheckCXXCompilerFlag)
set(CMAKE_REQUIRED_FLAGS "-fsanitize=fuzzer")
check_cxx_source_compiles(
  "#include <cstddef>
    extern \"C\" int LLVMFuzzerTestOneInput(const void *, size_t) { return 0; }"
  HAS_FUZZER)
set(CMAKE_REQUIRED_FLAGS "")

option(ENABLE_FUZZING "Enable fuzzing tests" ${HAS_FUZZER})
if(NOT ENABLE_FUZZING)
  message(STATUS "Will NOT build fuzzing tests (requires Clang 6 or newer)")
endif()

# --------------------------------------------------
# clang-tidy
# --------------------------------------------------
option(USE_CLANG_TIDY "Enable clang-tidy checks" OFF)
if(USE_CLANG_TIDY)
  message(STATUS "Clang-tidy build enabled")
  # read config from .clang-tidy
  set(CMAKE_CXX_CLANG_TIDY "clang-tidy;--config=")
endif()

# --------------------------------------------------
# Compiler flags
# --------------------------------------------------
# explicitly add -std=c++17 and -fno-rtti we have CMAKE_CXX_STANDARD, but for
# some reason it does not put the -std=c++17 or -std=gnu++17 to the flags on
# some systems. For the -fno-rtti: LLVM still got problems with turning RTTI
# off...
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++17")
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fno-rtti -Wall -Wextra")
if(NO_EXCEPTIONS)
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fno-exceptions")
endif()

if(USE_SANITIZERS)
  set(CMAKE_REQUIRED_FLAGS "-fsanitize=undefined,address") # for linker
  check_cxx_compiler_flag("-fsanitize=undefined,address" sanitizers_work)
  set(CMAKE_REQUIRED_FLAGS "")

  if(sanitizers_work)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fsanitize=undefined,address")
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -g -fno-omit-frame-pointer")
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fno-sanitize-recover=all")
    add_definitions(-DUSING_SANITIZERS)
  else()
    message(
      WARNING
        "Used compiler does not support sanitizers or its support is incomplete."
    )
  endif()
endif()

# Debug Release RelWithDebInfo MinSizeRel.
if(CMAKE_BUILD_TYPE STREQUAL "Debug")
  add_definitions(-DDEBUG_ENABLED)
  message(STATUS "Using compilation flags: ${CMAKE_CXX_FLAGS_DEBUG}")
elseif(CMAKE_BUILD_TYPE STREQUAL "Release")
  message(STATUS "Using compilation flags: ${CMAKE_CXX_FLAGS_RELEASE}")
elseif(CMAKE_BUILD_TYPE STREQUAL "RelWithDebInfo")
  message(STATUS "Using compilation flags: ${CMAKE_CXX_FLAGS_RELWITHDEBINFO}")
elseif(CMAKE_BUILD_TYPE STREQUAL "MinSizeRel")
  message(STATUS "Using compilation flags: ${CMAKE_CXX_FLAGS_MINSIZEREL}")
endif()

message(STATUS "Additional compilation flags: ${CMAKE_CXX_FLAGS}")

include(GNUInstallDirs)
message(STATUS "CMAKE_INSTALL_LIBDIR: \"${CMAKE_INSTALL_LIBDIR}\"")
message(STATUS "CMAKE_INSTALL_INCLUDEDIR: \"${CMAKE_INSTALL_INCLUDEDIR}\"")

include_directories(include)
include_directories(lib)

add_subdirectory(lib)
add_subdirectory(tools)
add_subdirectory(tests EXCLUDE_FROM_ALL)

if(NOT LLVM_DG)
  set(INSTALL_EXCLUDE_PATTERNS PATTERN "llvm" EXCLUDE)
endif()
install(
  DIRECTORY include/
  DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}
  ${INSTALL_EXCLUDE_PATTERNS})
