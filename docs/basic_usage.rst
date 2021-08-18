Basic usage
==============

yinyang is a mutation-based fuzzer, i.e. it mutates a set of seed formulas using a mutation strategy and then uses the mutated formulas as the test seeds for SMT solvers. yinyang can so detect soundness bugs, invalid model bugs, crashes, segfaults, etc. With ``typefuzz`` we generate mutants by generating fresh expressions from the ones from the seed and root them by operators such as ``=,distinct,+,-, *,/`` by one another. You can run yinyang with the ``typefuzz`` strategy using the following command:   

.. code-block:: bash
   
   $ typefuzz "<solver_clis>" <seed_path>

- ``<solver_clis>``: a sequence of SMT solvers command lines separated by semicolons. At least two SMT solvers command lines are necessary.  


- ``<seed_path>``: path to single seed or a directory containing the SMT-LIB seed files.   


**Example:**

.. code-block:: bash
    
    $ typefuzz "z3 model_validate=true;cvc4 --check-models -m -i -q" benchmarks 


yinyang will by default randomly select formulas from the folder ``./benchmarks``. By default SMT-LIB files larger than 20k will be ignored.  yinyang will generate 300 mutants per seed formula and will run in an infinite loop. You can use the shortcut ``CTRL+C`` to terminate yinyang manually. If a bug has been found, the bug trigger is stored in ``./bugs``.

.. note::
   To catch invalid model bugs, you have to supply options to enable model validation in ``<solver_clis>``. Also consider that you may need to supply options to enable model production and incremental mode to command lines in ``<solver_clis>``.

**Reducing a bug**.
After finding a bug, it is useful to produce a minimal test case before reporting the bug to save the SMT solver developers' time and effort. For many test cases, the C code reducer `creduce <https://embed.cs.utah.edu/creduce/>`_ does a great job. Besides, SMT-LIB specific reducer `pydelta <https://github.com/nafur/pydelta>`_ can be used.
