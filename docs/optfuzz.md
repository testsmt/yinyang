SMT solvers can usually be configured with command-line options, and the bugs can be triggered by the some combinations of the options. Thus, Yin-Yang supports option fuzzing along with [type-aware operator mutation](http://arxiv.org/pdf/2004.08799) and [semantic fusion](https://dl.acm.org/doi/pdf/10.1145/3385412.3385985). You can enable option fuzzing via `-optfuzz` with an option setting file.

The format of the options setting file is as follow:

```
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
```

`<solver keywords>` : Keywords for matching the solver command-line interfaces. If the keywords are found in the command-line interfaces, Yin-Yang will generate a corresponding random option setting.

`<option name>`: Name of the option item. 

`[type|value]*`: Type or value of the option. The type can be either `bool` or `int`. The value can be either `true`, `false`, or arbitrary integers. In default, i.e., leaving this position empty, the option is assigned to `bool` type. Optfuzz will generate a random value according to the type of the option.

`###`: Mark for splitting the option setting blocks. The options in different blocks are independent.

See example [option_setting.txt](../examples/option_setting.txt)
