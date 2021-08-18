Fuzzing setup
=============

SMT-LIB seeds 
..............

To select SMT-LIB seed files for fuzzing SMT solvers with yinyang, edit ``scripts/SMT-LIB-clone.sh`` to select the logics for testing. Then use the following command to download the chosen benchmarks.

.. code-block:: bash

    $ ./scripts/SMT-LIB-clone.sh 

Alternatively, you can download the benchmarks directly from the website of `SMT-LIB initiative <http://smtlib.cs.uiowa.edu/>`_ 
or use your own benchmarks.


SMT solvers
..............

To run typefuzz or opfuzz, you need to install two or more SMT solvers.   
The SMT-LIB initiative provides a comprehensive `list of SMT solvers <http://smtlib.cs.uiowa.edu/solvers.shtml>`_.
Make sure that all SMT solver you consider for testing supports the chosen seeds. 

If you can only use one SMT solver consider :doc:`fusion`.   
