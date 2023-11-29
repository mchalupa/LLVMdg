#ifndef DG_TOOL_LLVM_SLICER_H_
#define DG_TOOL_LLVM_SLICER_H_

#include <ctime>
#include <fstream>

#include <llvm/IR/Module.h>
#include <llvm/Support/raw_os_ostream.h>

#if LLVM_VERSION_MAJOR >= 4
#include <llvm/Bitcode/BitcodeReader.h>
#include <llvm/Bitcode/BitcodeWriter.h>
#else
#include <llvm/Bitcode/ReaderWriter.h>
#endif

#include "dg/llvm/LLVMDependenceGraph.h"
#include "dg/llvm/LLVMDependenceGraphBuilder.h"
#include "dg/llvm/LLVMSlicer.h"

#include "dg/llvm/LLVMDG2Dot.h"
#include "dg/llvm/LLVMDGAssemblyAnnotationWriter.h"

#include "dg/util/TimeMeasure.h"

#include "llvm-slicer-opts.h"
#include "llvm-slicer-utils.h"

/// --------------------------------------------------------------------
//   - Slicer class -
//
//  The main class that takes the bitcode, constructs the dependence graph
//  and then slices it w.r.t given slicing criteria.
//  The usual workflow is as follows:
//
//  Slicer slicer(M, options);
//  slicer.buildDG();
//  slicer.mark(criteria);
//  slicer.slice();
//
//  In the case that the slicer is not used for slicing,
//  but just for building the graph, the user may do the following:
//
//  Slicer slicer(M, options);
//  slicer.buildDG();
//  slicer.computeDependencies();
//
//  or:
//
//  Slicer slicer(M, options);
//  slicer.buildDG(true /* compute dependencies */);
//
/// --------------------------------------------------------------------
class Slicer {
    llvm::Module *M{};
    const SlicerOptions &_options;

    dg::llvmdg::LLVMDependenceGraphBuilder _builder;
    std::unique_ptr<dg::LLVMDependenceGraph> _dg{};

    dg::llvmdg::LLVMSlicer slicer;
    uint32_t slice_id = 0;
    const uint32_t _default_slice_id = 0xdead;
    bool _computed_deps{false};

  public:
    Slicer(llvm::Module *mod, const SlicerOptions &opts)
            : M(mod), _options(opts), _builder(mod, _options.dgOptions) {
        assert(mod && "Need module");
    }

    const dg::LLVMDependenceGraph &getDG() const { return *_dg; }
    dg::LLVMDependenceGraph &getDG() { return *_dg; }

    const SlicerOptions &getOptions() const { return _options; }

    // Mirror LLVM to nodes of dependence graph,
    // No dependence edges are added here unless the
    // 'compute_deps' parameter is set to true.
    // Otherwise, dependencies must be computed later
    // using computeDependencies().
    bool buildDG(bool compute_deps = false) {
        _dg = std::move(_builder.constructCFGOnly());

        if (!_dg) {
            llvm::errs() << "Building the dependence graph failed!\n";
            return false;
        }

        if (compute_deps)
            computeDependencies();

        return true;
    }

    // Explicitely compute dependencies after building the graph.
    // This method can be used to compute dependencies without
    // calling mark() afterwards (mark() calls this function).
    // It must not be called before calling mark() in the future.
    void computeDependencies() {
        assert(!_computed_deps && "Already called computeDependencies()");
        // must call buildDG() before this function
        assert(_dg && "Must build dg before computing dependencies");

        _dg = _builder.computeDependencies(std::move(_dg));
        _computed_deps = true;

        const auto &stats = _builder.getStatistics();
        llvm::errs() << "[llvm-slicer] CPU time of pointer analysis: "
                     << double(stats.ptaTime) / CLOCKS_PER_SEC << " s\n";
        llvm::errs() << "[llvm-slicer] CPU time of data dependence analysis: "
                     << double(stats.rdaTime) / CLOCKS_PER_SEC << " s\n";
        llvm::errs()
                << "[llvm-slicer] CPU time of control dependence analysis: "
                << double(stats.cdaTime) / CLOCKS_PER_SEC << " s\n";
    }

    // Mark the nodes from the slice.
    // This method calls computeDependencies(),
    // but buildDG() must be called before.
    bool mark(std::set<dg::LLVMNode *> &criteria_nodes) {
        assert(_dg && "mark() called without the dependence graph built");
        assert(!criteria_nodes.empty() && "Do not have slicing criteria");

        dg::debug::TimeMeasure tm;

        // compute dependece edges
        computeDependencies();

        // unmark this set of nodes after marking the relevant ones.
        // Used to mimic the Weissers algorithm
        std::set<dg::LLVMNode *> unmark;

        if (_options.removeSlicingCriteria)
            unmark = criteria_nodes;

        _dg->getCallSites(_options.additionalSlicingCriteria, &criteria_nodes);

        for (const auto &funcName : _options.preservedFunctions)
            slicer.keepFunctionUntouched(funcName.c_str());

        slice_id = _default_slice_id;

        tm.start();
        for (dg::LLVMNode *start : criteria_nodes)
            slice_id = slicer.mark(start, slice_id, _options.forwardSlicing);

        assert(slice_id != 0 && "Somethig went wrong when marking nodes");

        // if we have some nodes in the unmark set, unmark them
        for (dg::LLVMNode *nd : unmark)
            nd->setSlice(0);

        tm.stop();
        tm.report("[llvm-slicer] Finding dependent nodes took");

        return true;
    }

    bool slice() {
        assert(_dg && "Must run buildDG() and computeDependencies()");
        assert(slice_id != 0 && "Must run mark() method before slice()");

        dg::debug::TimeMeasure tm;

        tm.start();
        slicer.slice(_dg.get(), nullptr, slice_id);

        tm.stop();
        tm.report("[llvm-slicer] Slicing dependence graph took");

        dg::SlicerStatistics &st = slicer.getStatistics();
        llvm::errs() << "[llvm-slicer] Sliced away " << st.nodesRemoved
                     << " from " << st.nodesTotal << " nodes in DG\n";

        return true;
    }

    ///
    // Create new empty main in the module. If 'call_entry' is set to true,
    // then call the entry function from the new main (if entry is not main),
    // otherwise the main is going to be empty
    bool createEmptyMain(bool call_entry = false) {
        llvm::LLVMContext &ctx = M->getContext();
        llvm::Function *main_func = M->getFunction("main");
        if (!main_func) {
            auto C = M->getOrInsertFunction("main", llvm::Type::getInt32Ty(ctx)
#if LLVM_VERSION_MAJOR < 5
                                                            ,
                                            nullptr
#endif // LLVM < 5
            );
#if LLVM_VERSION_MAJOR < 9
            if (!C) {
                llvm::errs() << "Could not create new main function\n";
                return false;
            }

            main_func = llvm::cast<llvm::Function>(C);
#else
            main_func = llvm::cast<llvm::Function>(C.getCallee());
#endif
        } else {
            // delete old function body
            main_func->deleteBody();
        }

        assert(main_func && "Do not have the main func");
        assert(main_func->empty() && "The main func is not empty");

        // create new function body
        llvm::BasicBlock *blk =
                llvm::BasicBlock::Create(ctx, "entry", main_func);

        if (call_entry && _options.dgOptions.entryFunction != "main") {
            llvm::Function *entry =
                    M->getFunction(_options.dgOptions.entryFunction);
            assert(entry && "The entry function is not present in the module");

            // TODO: we should set the arguments to undef
            llvm::CallInst::Create(entry, "entry", blk);
        }

        llvm::Type *Ty = main_func->getReturnType();
        llvm::Value *retval = nullptr;
        if (Ty->isIntegerTy())
            retval = llvm::ConstantInt::get(Ty, 0);
        llvm::ReturnInst::Create(ctx, retval, blk);

        return true;
    }
};

class ModuleWriter {
    const SlicerOptions &options;
    llvm::Module *M;

  public:
    ModuleWriter(const SlicerOptions &o, llvm::Module *m) : options(o), M(m) {}

    int cleanAndSaveModule(bool should_verify_module = true) {
        // remove unneeded parts of the module
        removeUnusedFromModule();

        // fix linkage of declared functions (if needs to be fixed)
        makeDeclarationsExternal();

        return saveModule(should_verify_module);
    }

    int saveModule(bool should_verify_module = true) {
        if (should_verify_module)
            return verifyAndWriteModule();
        return writeModule();
    }

    void removeUnusedFromModule() {
        bool fixpoint;

        do {
            fixpoint = _removeUnusedFromModule();
        } while (fixpoint);
    }

    // after we slice the LLVM, we somethimes have troubles
    // with function declarations:
    //
    //   Global is external, but doesn't have external or dllimport or weak
    //   linkage! i32 (%struct.usbnet*)* @always_connected invalid linkage type
    //   for function declaration
    //
    // This function makes the declarations external
    void makeDeclarationsExternal() {
        using namespace llvm;

        // iterate over all functions in module
        for (auto &F : *M) {
            if (F.empty()) {
                // this will make sure that the linkage has right type
                F.deleteBody();
            }
        }
    }

  private:
    bool writeModule() {
        // compose name if not given
        std::string fl;
        if (!options.outputFile.empty()) {
            fl = options.outputFile;
        } else {
            fl = options.inputFile;
            replace_suffix(fl, ".sliced");
        }

        // open stream to write to
        std::ofstream ofs(fl);
        llvm::raw_os_ostream ostream(ofs);

        // write the module
        llvm::errs() << "[llvm-slicer] saving sliced module to: " << fl.c_str()
                     << "\n";

#if (LLVM_VERSION_MAJOR > 6)
        llvm::WriteBitcodeToFile(*M, ostream);
#else
        llvm::WriteBitcodeToFile(M, ostream);
#endif

        return true;
    }

    bool verifyModule() {
        // the verifyModule function returns false if there
        // are no errors

#if ((LLVM_VERSION_MAJOR >= 4) || (LLVM_VERSION_MINOR >= 5))
        return !llvm::verifyModule(*M, &llvm::errs());
#else
        return !llvm::verifyModule(*M, llvm::PrintMessageAction);
#endif
    }

    int verifyAndWriteModule() {
        if (!verifyModule()) {
            llvm::errs() << "[llvm-slicer] ERROR: Verifying module failed, the "
                            "IR is not valid\n";
            llvm::errs()
                    << "[llvm-slicer] Saving anyway so that you can check it\n";
            return 1;
        }

        if (!writeModule()) {
            llvm::errs() << "Saving sliced module failed\n";
            return 1;
        }

        // exit code
        return 0;
    }

    bool _removeUnusedFromModule() {
        using namespace llvm;
        // do not slice away these functions no matter what
        // FIXME do it a vector and fill it dynamically according
        // to what is the setup (like for sv-comp or general..)
        const char *keep[] = {options.dgOptions.entryFunction.c_str()};

        // when erasing while iterating the slicer crashes
        // so set the to be erased values into container
        // and then erase them
        std::set<Function *> funs;
        std::set<GlobalVariable *> globals;
        std::set<GlobalAlias *> aliases;

        for (auto &I : *M) {
            Function *func = &I;
            if (array_match(func->getName(), keep))
                continue;

            // if the function is unused or we haven't constructed it
            // at all in dependence graph, we can remove it
            // (it may have some uses though - like when one
            // unused func calls the other unused func
            if (func->hasNUses(0))
                funs.insert(func);
        }

        for (auto I = M->global_begin(), E = M->global_end(); I != E; ++I) {
            GlobalVariable *gv = &*I;
            if (gv->hasNUses(0))
                globals.insert(gv);
        }

        for (GlobalAlias &ga : M->aliases()) {
            if (ga.hasNUses(0))
                aliases.insert(&ga);
        }

        for (Function *f : funs)
            f->eraseFromParent();
        for (GlobalVariable *gv : globals)
            gv->eraseFromParent();
        for (GlobalAlias *ga : aliases)
            ga->eraseFromParent();

        return (!funs.empty() || !globals.empty() || !aliases.empty());
    }
};

class DGDumper {
    const SlicerOptions &options;
    LLVMDependenceGraph *dg;
    bool bb_only{false};
    uint32_t dump_opts{debug::PRINT_DD | debug::PRINT_CD | debug::PRINT_USE |
                       debug::PRINT_ID};

  public:
    DGDumper(const SlicerOptions &opts, LLVMDependenceGraph *dg,
             bool bb_only = false,
             uint32_t dump_opts = debug::PRINT_DD | debug::PRINT_CD |
                                  debug::PRINT_USE | debug::PRINT_ID)
            : options(opts), dg(dg), bb_only(bb_only), dump_opts(dump_opts) {}

    void dumpToDot(const char *suffix = nullptr) {
        // compose new name
        std::string fl(options.inputFile);
        if (suffix)
            replace_suffix(fl, suffix);
        else
            replace_suffix(fl, ".dot");

        llvm::errs() << "[llvm-slicer] Dumping DG to " << fl << "\n";

        if (bb_only) {
            debug::LLVMDGDumpBlocks dumper(dg, dump_opts, fl.c_str());
            dumper.dump();
        } else {
            debug::LLVMDG2Dot dumper(dg, dump_opts, fl.c_str());
            dumper.dump();
        }
    }
};

namespace {
inline std::string undefFunsBehaviorToStr(dg::dda::UndefinedFunsBehavior b) {
    using namespace dg::dda;
    if (b == PURE)
        return "pure";

    std::string ret;
    if (b & (WRITE_ANY | WRITE_ARGS)) {
        ret = "write ";
        if (b & WRITE_ANY) {
            if (b & WRITE_ARGS) {
                ret += "any+args";
            } else {
                ret += "any";
            }
        } else if (b & WRITE_ARGS) {
            ret += "args";
        }
    }
    if (b & (READ_ANY | READ_ARGS)) {
        if (b & (WRITE_ANY | WRITE_ARGS)) {
            ret += " read ";
        } else {
            ret = "read ";
        }

        if (b & READ_ANY) {
            if (b & READ_ARGS) {
                ret += "any+args";
            } else {
                ret += "any";
            }
        } else if (b & READ_ARGS) {
            ret += "args";
        }
    }

    return ret;
}
} // anonymous namespace

class ModuleAnnotator {
    using AnnotationOptsT =
            dg::debug::LLVMDGAssemblyAnnotationWriter::AnnotationOptsT;

    const SlicerOptions &options;
    LLVMDependenceGraph *dg;
    AnnotationOptsT annotationOptions;

  public:
    ModuleAnnotator(const SlicerOptions &o, LLVMDependenceGraph *dg,
                    AnnotationOptsT annotO)
            : options(o), dg(dg), annotationOptions(annotO) {}

    bool shouldAnnotate() const { return annotationOptions != 0; }

    void annotate(const std::set<LLVMNode *> *criteria = nullptr) {
        // compose name
        std::string fl(options.inputFile);
        replace_suffix(fl, "-debug.ll");

        // open stream to write to
        std::ofstream ofs(fl);
        llvm::raw_os_ostream outputstream(ofs);

        std::string module_comment =
                "; -- Generated by llvm-slicer --\n"
                ";   * slicing criteria: '" +
                options.slicingCriteria + "'\n" +
                ";   * legacy slicing criteria: '" +
                options.legacySlicingCriteria + "'\n" +
                ";   * legacy secondary slicing criteria: '" +
                options.legacySecondarySlicingCriteria + "'\n" +
                ";   * forward slice: '" +
                std::to_string(options.forwardSlicing) + "'\n" +
                ";   * remove slicing criteria: '" +
                std::to_string(options.removeSlicingCriteria) + "'\n" +
                ";   * undefined functions behavior: '" +
                undefFunsBehaviorToStr(
                        options.dgOptions.DDAOptions.undefinedFunsBehavior) +
                "'\n" + ";   * pointer analysis: ";

        using AnalysisType = LLVMPointerAnalysisOptions::AnalysisType;
        switch (options.dgOptions.PTAOptions.analysisType) {
        case AnalysisType::fi:
            module_comment += "flow-insensitive\n";
            break;
        case AnalysisType::fs:
            module_comment += "flow-sensitive\n";
            break;
        case AnalysisType::inv:
            module_comment += "flow-sensitive with invalidate\n";
            break;
        case AnalysisType::svf:
            module_comment += "SVF\n";
            break;
        }

        module_comment += ";   * PTA field sensitivity: ";
        if (options.dgOptions.PTAOptions.fieldSensitivity == Offset::UNKNOWN)
            module_comment += "full\n\n";
        else
            module_comment +=
                    std::to_string(
                            *options.dgOptions.PTAOptions.fieldSensitivity) +
                    "\n\n";

        llvm::errs() << "[llvm-slicer] Saving IR with annotations to " << fl
                     << "\n";
        auto *annot = new dg::debug::LLVMDGAssemblyAnnotationWriter(
                annotationOptions, dg->getPTA(), dg->getDDA(), criteria);
        annot->emitModuleComment(std::move(module_comment));
        llvm::Module *M = dg->getModule();
        M->print(outputstream, annot);

        delete annot;
    }
};

#endif // DG_TOOL_LLVM_SLICER_H_
