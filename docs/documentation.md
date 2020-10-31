Yin-Yang provides the following arguments to configure the fuzzing process:

```
-h, --help            show this help message and exit

-s {opfuzz,fusion}, --strategy {opfuzz,fusion}
                    set fuzzing strategy (default: opfuzz)

-o {sat,unsat}, --oracle {sat,unsat}
                    set oracle for semantic fusion strategy (default: unknown)

-i ITERATIONS, --iterations ITERATIONS
                    set mutating iterations for each seed/pair (default: 30)

-t TIMEOUT, --timeout TIMEOUT
                    set timeout for solving process (default: 8)

-optfuzz OPTFUZZ, --optfuzz OPTFUZZ
                    read solvers' options setting and enable option fuzzing

-name NAME, --name NAME
                    set name of this fuzzing instance (default: random string)

-bugs BUGSFOLDER, --bugsfolder BUGSFOLDER
                    set bug folder (default: ./bugs)

-scratch SCRATCHFOLDER, --scratchfolder SCRATCHFOLDER
                    set scratch folder (default: ./scratch)
```

Note that Yin-Yang supports two strategies for fuzzing SMT solver: [type-aware operator mutation](http://arxiv.org/pdf/2004.08799) and [semantic fusion](https://dl.acm.org/doi/pdf/10.1145/3385412.3385985), you can appoint the strategy by using `-s`. Semantic fusion has to be used along with `-o` to specify the test oracle. Note that the satisfiability of the seeds for [semantic fusion](https://dl.acm.org/doi/pdf/10.1145/3385412.3385985) should be the same as the oracle. In default, Yin-Yang uses [type-aware operator mutation](http://arxiv.org/pdf/2004.08799). Currently, [semantic fusion](https://dl.acm.org/doi/pdf/10.1145/3385412.3385985) supports LIA, LRA, NRA, QF_LIA, QF_LRA, QF_NRA, QF_SLIA, QF_S logics, more logics supports are being developed.


SMT solvers can usually be configured with command-line options, and the bugs can be triggered by the some combinations of the options. Thus, Yin-Yang supports option fuzzing along with [type-aware operator mutation](http://arxiv.org/pdf/2004.08799) and [semantic fusion](https://dl.acm.org/doi/pdf/10.1145/3385412.3385985). You can enable option fuzzing via `-optfuzz` with an option setting file. See more details in [optfuzz.md](./optfuzz.md). 
