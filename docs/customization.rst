Customization
=============

Options 
.........

yinyang provides the following options. Please consult ``python3 yinyang.py --help`` for a full list.

* ``-i --iterations ITERATIONS``: the number of iterations on each individual seed. (default: 300)  
* ``-m --modulo MODULO``: specifies how often the mutants will be forwarded to the SMT solvers. For example, with 300 iterations and 2 as a modulo, 150 mutants per seed file will be passed to the SMT solvers. High modulo and iteration counts, prioritize deeper mutations. (default: 2) 
* ``-t --timeout TIMEOUT``: imposes a timeout limit (in seconds) on each SMT solver for solving  mutant formula (default: 8) 
* ``-d, --diagnose``: forwards solver outputs to stdout e.g. for solver command line diagnosis
* ``-bugs BUGSFOLDER`` (default: ./bugs) 
* ``-scratch SCRATCHFOLDER``: specifies where the mutant formulas are temporarily stored. Note, if you run yinyang with several processes in parallel, each instance should have its own scratch folder. (default: ./scratch)      
* ``-s --strategy {opfuzz,fusion}`` sets the mutation strategy. For more details on ``fusion``, see :doc:`fusion`  (default: opfuzz).
* ``-km --keep-mutants``: do not delete the mutants from the scratch folder. Warning: beware that this can quickly exhaust your entire disk space.              
                        

Customize solvers configurations  
.................................
If you want to test several SMT solver configuration at once the putting them  as a commandline argument like ``python3 yinyang.py "<solver_clis>" <seed_path>`` may be inconvenient to you. Instead you can modify the solver list in ``config/config.py``.  
As an example consider:

.. code-block:: python3

    solvers = [                                                                        
        "z3 model_validate=true",                                               
        "z3 model_validate=true smt.arith.solver=2",                            
        "z3 model_validate=true smt.arith.solver=3",                            
        "z3 model_validate=true smt.arith.solver=6",                            
        "cvc4 --check-models --produce-models --incremental --strings-exp -q",         
    ] 

You can then use ``python3 yinyang.py "" <seed_path>`` to run run these five different solver configurations.    

Option fuzzing
.......................

Customize bug detection  
.........................
yinyang's bug detection logic is based on three lists: ``crash_list, duplicate_list, ignore_list`` of ``config/config.py`` which you can customize. yinyang detects crash bugs by matching the stdout and stderr of the solvers in the ``crash_list`` . If yinyang detects a bug this way, it subsequently matches the crash message against all strings in ``duplicate_list``. The ``duplicate_list`` is useful to filter out repeatedly occurring bugs from getting copied to ``./bugs``.  The ``ignore_list`` can be used to filter out errors occurring in a solver call.  By default yinyang detects mutants returning non-zero exit codes as crashes except those that match with the ``ignore_list```.        


The below setup shows the three list in ``config/config.py`` that worked well in practice for Z3 and CVC4. 

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



Customizing mutations 
...............................

To customize ``opfuzz``'s mutations, you can edit ``config/operator_mutations.txt``.

.. code-block:: bash 

    =,distinct
    exists,forall
    not -> and,or
    and,or,=> :arity 3+
    and,or,=>,xor :arity 2
    <=,>=,<,>
    +,-,* :arity 2+
    mod,div
    abs,- :arity 1
    re.++,re.union,re.inter,re.diff
    str.<=,str.<,str.prefixof,str.suffixof,str.contains
    str.replace,str.replace_all
    str.replace_re,str.replace_re_all
    re.comp,re.+,re.opt,re.*
    re.none,re.all,re.allchar
    str.to_code,str.to_int
    str.from_code,str.from_int
    union,intersection,setminus
    bvnot,bvneg
    bvand,bvor,bvnand,bvnor,bvxor,bvxnor,bvsub,bvsdiv,bvsmod,bvadd,bvmul,bvudiv,bvurem,bvshl,bvlshr,bvashr
    bvule,bvugt,bvuge,bvslt,bvsle,bvsgt,bvsge
    fp.abs,fp.neg
    fp.add,fp.sub,fp.mul,fp.div
    fp.min,fp.max
    fp.leq,fp.lt,fp.geq,fp.gt,fp.eq
    fp.isNormal,fp.isSubnormal,fp.isZero,fp.isInfinite,fp.isNaN,fp.isNegative,fp.isPositive

**Format:**

.. code-block:: bash

    op1, op2, ... ,op_n

    Operators op_i in the same line form an equivalence class and can mutually 
    replace each other. 

    ; Example:
     +, -, * 
    ;
    ; Operator mutations can be conditioned on operator's arity. 
    ; 
    ; Example: 
    ; =,distinct: arity: 2+ 
    ; -,abs: arity: 1- 
    ;
    ; This requires operators "=" and "distinct" to have at least two arguments to trigger the  
    ; mutation, and "-","abs" to have at most one argument. At the moment, only the arities  
    ; 2+ ("two or more") and 1- (one or less) are supported  
    ; 
    ; Unidirectional mutations can be specified as   
    ; 
    ; abs -> - 
    ;
    ; which corresponds to a one-way mutation from operator "abs" to operator "-" 


