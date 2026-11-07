Fuzzing setup
=============

SMT-LIB seeds 
..............

To download SMT-LIB seed files for fuzzing SMT solvers with yinyang, pass the logics for testing to ``scripts/SMT-LIB-clone.sh``. It downloads the non-incremental benchmarks of these logics from the latest SMT-LIB release on Zenodo to ``non-incremental/<logic>`` (it needs curl, tar and zstd):

.. code-block:: bash

    $ ./scripts/SMT-LIB-clone.sh QF_LIA QF_BV

Without arguments, the script lists the logics of the release. Set ``INCREMENTAL=1`` for the incremental benchmarks (in ``incremental/<logic>``) and ``RELEASE`` (2023, 2024 or 2025) or ``RECORD`` (a Zenodo record) for another release.

Alternatively, you can download the benchmarks directly from the website of `SMT-LIB initiative <http://smtlib.cs.uiowa.edu/>`_ 
or use your own benchmarks.


SMT solvers
..............

To run typefuzz or opfuzz, you need to install two or more SMT solvers.   
The SMT-LIB initiative provides a comprehensive `list of SMT solvers <http://smtlib.cs.uiowa.edu/solvers.shtml>`_.
Make sure that all SMT solvers you consider for testing support the chosen seeds. 

If you can only use one SMT solver consider :doc:`fusion`.   
