Customization
=============

Options 
.........

yinyang provides the following options. Please consult ``python3 yinyang.py --help`` for a full list.

* ``-i --iterations ITERATIONS`` the number of iterations on each seed. (default: 300)  
* ``-m --modulo MODULO`` specifies how often the mutants will be forwarded to the SMT solvers. For example, with 300 iterations and 2 as a modulo, 150 mutants per seed file will be passed to the SMT solvers. High modulo and iteration counts prioritize deeper mutations. (default: 2) 
* ``-t --timeout TIMEOUT`` imposes a timeout limit (in seconds) on each SMT solver for solving  mutant formula. (default: 8) 
* ``-d, --diagnose`` forwards solver outputs to stdout e.g. for solver command line diagnosis. 
* ``-bugs BUGSFOLDER`` (default: ./bugs) 
* ``-scratch SCRATCHFOLDER`` specifies where the mutant formulas are temporarily stored. Note, if you run yinyang with several processes in parallel, each instance should have its own scratch folder. (default: ./scratch)      
* ``-s --strategy {opfuzz,fusion}`` sets the mutation strategy. For more details on fusion, see :doc:`fusion`.  (default: opfuzz)
* ``-km --keep-mutants`` do not delete the mutants from the scratch folder. Warning: beware that this can quickly exhaust your entire disk space.
* ``-q --quiet`` do not output statistics and other output.
* ``-fl", "--file-size-limit`` file size limit on seed formula in bytes. (default: 20000)


                        

Customize solvers configurations  
.................................
If you want to test several SMT solver configurations at once the putting them  as a commandline argument like ``python3 yinyang.py "<solver_clis>" <seed_path>`` may be inconvenient to you. Instead, you can modify the solver list in ``config/config.py``.  
As an example consider:

.. code-block:: python3

    solvers = [                                                                        
        "z3 model_validate=true",                                               
        "z3 model_validate=true smt.arith.solver=2",                            
        "z3 model_validate=true smt.arith.solver=3",                            
        "z3 model_validate=true smt.arith.solver=6",                            
        "cvc4 --check-models --produce-models --incremental --strings-exp -q",         
    ] 

You can then use ``python3 yinyang.py "" <seed_path>`` to run the above five solver configurations.    

Option fuzzing
.......................
If you want to test many options of an SMT solver with yinyang, you can turn on option fuzzing via ``-optfuzz <file>`` with configuration file ``config/option_setting.txt`` specifying the options. This will randomly add ``set-option`` commands to the mutants.    

**Format:**

.. code-block:: text 

    <solver keywords>
    <option name> [type|value]*
    <option name> [type|value]*
    ###
    <solver keywords>
    <option name> [type|value]*
    <option name> [type|value]*
    ###
    <solver keywords>
    <option name> [type|value]*
    <option name> [type|value]*

- ``<solver keywords>``  Keywords for matching the solver command lines. If the keywords can be matched.

- ``<option name>``: Name of the option item. 

- ``[type|value]*``: Type or value of the option. The type can be either `bool` or `int` and the value can be either `true`, `false`, or an integer. By default, i.e., by leaving this position empty, the option is assigned to be `bool`. 

- ``###``: Splits option blocks. The options in different blocks are independent.


Customize bug detection  
.........................
yinyang's bug detection logic is based on three lists: ``crash_list, duplicate_list, ignore_list`` of ``config/config.py`` which you can customize. yinyang detects crash bugs by matching the stdout and stderr of the solvers in with the strings in the list``crash_list``. If yinyang detects a bug this way, it subsequently matches the crash message against all strings in ``duplicate_list``. The ``duplicate_list`` is useful to filter out repeatedly occurring bugs from getting copied to ``./bugs``.  The ``ignore_list`` can be used to filter out errors occurring in a solver call.  By default yinyang detects mutants returning non-zero exit codes as crashes except those that match with the ``ignore_list``.        


The below setup shows the three lists in ``config/config.py`` that worked well in practice with Z3 and CVC4. 

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

To customize ``opfuzz``'s mutations, you can edit ``config/operator_mutations.txt``. An operator mutation can be bidirectional or unidirectional and may be conditioned on the arity of the operator.

**Format:**

.. code-block:: text 

 [<op_name>, ..., <op_name> [arity: k[+,-]]]*
 [<op_name> -> <op_name> [arity: k[+,-]]]*

    
where ``k`` is a positive integer, ``+`` indicates at least one and ``-`` indicates at most one.   

**Example:**


.. code-block:: text 
    
    +, -, * 
    =,distinct: arity: 2+ 
    -,abs: arity: 1- 
    abs -> - 


Line 1: Operators ``+, -, *`` in the same line form an equivalence class and can bidirectionally replace each other. 

Line 2+3: Operator mutations conditioned on arity. This requires operators ``=`` and ``distinct`` to have at least two arguments to trigger the  mutation, and ``-``, ``abs`` to have at most one argument.

Line 4:  Unidirectional from operator ``abs`` to operator ``-``.

