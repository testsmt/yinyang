Customization
=============

Options 
.........
  -i ITERATIONS, --iterations ITERATIONS
                        set mutating iterations for each seed/pair (default: 300 for Type-Aware Operator Mutation, 30 for
                        SemanticFusion)
  -m MODULO, --modulo MODULO
                        determines when the mutant will be forwarded to the solvers for opfuzz
  -t TIMEOUT, --timeout TIMEOUT
                        set timeout for solving process (default: 8)
  -d, --diagnose        forward solver outputs to stdout e.g. for solver cli diagnosis
  -optfuzz OPTFUZZ, --optfuzz OPTFUZZ
                        read solvers' option setting and enable option fuzzing
  -name NAME, --name NAME
                        set name of this fuzzing instance (default: random string)
  -bugs BUGSFOLDER, --bugsfolder BUGSFOLDER
                        set bug folder (default: /Users/windomin/repositories/yinyang_private/bugs)
  -scratch SCRATCHFOLDER, --scratchfolder SCRATCHFOLDER
                        set scratch folder (default: /Users/windomin/repositories/yinyang_private/scratch)
  -opconfig OPCONFIG, --opconfig OPCONFIG
                        set operator mutation configuration (default:
                        /Users/windomin/repositories/yinyang_private/config/operator_mutations.txt)
  -fusionfun FUSIONFUN, --fusionfun FUSIONFUN
                        set fusion function configuration (default:
                        /Users/windomin/repositories/yinyang_private/config/fusion_functions.txt)
  -km, --keep-mutants   Do not delete the mutants generated in the scratchfolder.



Customize solvers 
.......................


Option fuzzing
.......................

Customize bug detection  
.........................

.. code-block:: python3

    # Solver configurations list to be used for fuzzing.                            
    solvers = []                                                                    
                                                                                
    # Crash list: crash messages emitted by solvers to consider as bugs.            
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
                                                                                   
    # Duplicate list: crash messages emitted by solvers to be considered duplicates,
    # i.e. will be ignored during fuzzing.                                             
    duplicate_list = [                                                                 
                                                                                       
    ]                                                                                  
                                                                                   
    # Ignore list: error messages emitted by solvers to be ignored.                    
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



Customize operator mutations 
...............................

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


