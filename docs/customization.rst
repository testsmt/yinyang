Customization
=============

Options 
.........

yinyang provides the following options. Please consult ``typefuzz --help`` for a full list.

* ``-i --iterations ITERATIONS`` the number of iterations on each seed. (default: 300)  
* ``-m --modulo MODULO`` specifies how often the mutants will be forwarded to the SMT solvers. For example, with 300 iterations and 2 as a modulo, 150 mutants per seed file will be passed to the SMT solvers. High modulo and iteration counts prioritize deeper mutations. (default: 2) 
* ``-t --timeout TIMEOUT`` imposes a timeout limit (in seconds) on each SMT solver for solving  mutant formula. (default: 8) 
* ``-d, --diagnose`` forwards solver outputs to stdout e.g. for solver command line diagnosis. 
* ``-bugs BUGSFOLDER`` (default: ./bugs) 
* ``-scratch SCRATCHFOLDER`` specifies where the mutant formulas are temporarily stored. Note, if you run yinyang with several processes in parallel, each instance should have its own scratch folder. (default: ./scratch)      
* ``-km --keep-mutants`` do not delete the mutants from the scratch folder. Warning: beware that this can quickly exhaust your entire disk space.
* ``-q --quiet`` do not output statistics and other output.
* ``-fl", "--file-size-limit`` file size limit on seed formula in bytes. (default: 20000)



Customize solvers configurations  
.................................
If you want to test several SMT solver configurations at once the putting them  as a commandline argument like ``typefuzz "<solver_clis>" <seed_path>`` may be inconvenient to you. Instead, you can modify the solver list in ``.yinyang/Config.py``. The directory file need to be created by the user.   

As an example consider:

.. code-block:: python3

    solvers = [                                                                        
        "z3 model_validate=true",                                               
        "z3 model_validate=true smt.arith.solver=2",                            
        "z3 model_validate=true smt.arith.solver=3",                            
        "z3 model_validate=true smt.arith.solver=6",                            
        "cvc4 --check-models --produce-models --incremental --strings-exp -q",         
    ] 

You can then use ``typefuzz "" <seed_path>`` to run the above five solver configurations.


Customize bug detection  
.........................
yinyang's bug detection logic is based on three lists: ``crash_list, duplicate_list, ignore_list`` of ``.yinyang/Config.py`` which you can customize. yinyang detects crash bugs by matching the stdout and stderr of the solvers in with the strings in the list``crash_list``. If yinyang detects a bug this way, it subsequently matches the crash message against all strings in ``duplicate_list``. The ``duplicate_list`` is useful to filter out repeatedly occurring bugs from getting copied to ``./bugs``.  The ``ignore_list`` can be used to filter out errors occurring in a solver call.  By default yinyang detects mutants returning non-zero exit codes as crashes except those that match with the ``ignore_list``.        


The below setup shows the three lists in ``.yinyang/Config.py`` that worked well in practice with Z3 and CVC4. 

.. code-block:: python3

    crash_list = [
        "Exception",
        "lang.AssertionError",
        "lang.Error",
        "runtime error",
        "LEAKED",
        "Leaked",
        "Segmentation fault",
        "segmentation fault",
        "segfault",
        "ASSERTION",
        "Assertion",
        "Fatal failure",
        "Internal error detected",
        "an invalid model was generated",
        "Failed to verify",
        "failed to verify",
        "ERROR: AddressSanitizer:",
        "invalid expression",
        "Aborted"
    ]

    duplicate_list = [

    ]

    ignore_list = [
       "(error ",
        "unexpected char",
        "failed to open file",
        "Expected result sat but got unsat",
        "Expected result unsat but got sat",
        "Parse Error",
        "Cannot get model",
        "Symbol 'str.to-re' not declared as a variable",
        "Symbol 'str.to.re' not declared as a variable",
        "Unimplemented code encountered",
    ]
