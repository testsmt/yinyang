Fusion
===============
Fusion is a metamorphic testing approach than can work with a single SMT solver.If multiple suitable SMT solvers are available for your use-case, we recommend using ``opfuzz`` instead.     


Basic Idea
...........
The basic idea behind fusion is to fuse formula pairs into a new formula of known satisfiability (either both sat or both unsat).  Given two seed formulas :math:`\varphi_1`, :math:`\varphi_2` and variables :math:`x, y` of :math:`\varphi_1` and :math:`\varphi_2` respectively, the idea is to 

1. Concatenate the formulas :math:`\varphi_1` and :math:`\varphi_2`
2. Add a fresh variable :math:`z = f(x,y)` 
3. Replace random occurrences of :math:`x = g_x(y)` and :math:`y = g_y(x)` within the concatenated formula

We call :math:`f` a fusion function and :math:`g_x, g_y` inversion functions.   

Usage
......

.. code-block:: bash

    $ python3 yinyang.py "<solver_clis>" -o <oracle> -s fusion <seed_path1> <seed_path2>
    $ python3 yinyang.py "<solver_clis>" -o <oracle> -s fusion <seed_path> 

where

* ``<solver_clis>`` a sequence of SMT solver commandlines separated by semicolons `;`. Note, since Fusion is a metamorphic testing approach, one SMT solver is sufficient.

* ``<oracle>`` desired test oracle result {sat, unsat}.


* ``<seed_path1>, <seed_path2>`` SMT-LIB v2.6 file of the same satisfiability, i.e. both either sat or unsat in accordance with the oracle.

* ``<seed_path>`` path to single seed or directory containing the SMT-LIB seed files, all of the same satisifiability.   
 

**Examples:**

.. code-block:: bash

   $ python3 yinyang.py "z3" -o sat -s fusion examples/phi1.smt2 examples/phi2.smt2

yinyang will test z3 by running fusion with 30 iterations on the two satisfiable seed formulas. The mutants generated yinyang will then be by construction satisfiable. In turn, with unsat as an oracle and two unsatisfiable seed formulas, fusion will generate unsatisfiable formulas.   


.. code-block:: bash

   $ python3 yinyang.py "z3" -o unsat -s fusion examples/phi3.smt2 examples/phi4.smt2


Seeds
......
Fusion requires the seeds that are pre-categorized to be either sat or unsat. Pre-categorized SMT-LIB scripts are available in the `following repository <https://github.com/testsmt/semantic-fusion-seeds>`_. Fusion currently only supports non-incremental mode, e.g.  LIA, LRA, NRA, QF_LIA, QF_LRA, QF_NRA, QF_SLIA, QF_S, etc. Fusion's applicability is constraint by the fusion function used.   


Fusion functions
................................
The configuration file ``yinyang/config/fusion_functions.txt`` specifies fusion and inversion functions.  The format is the following:  

.. code-block:: text 

    #begin  
    <declaration of x>
    <declaration of y>
    <declaration of z>
    [<declaration of c>]
    <assert fusion function>
    <assert inversion function> 
    <assert inversion function> 
    #end

**Example:**

The following code shows schematically fusion and inversion are described in ``yinyang/config/fusion_functions.txt``.

.. code-block:: text 

    #begin
    (declare-const x Int)
    (declare-const y Int)
    (declare-const z Int)
    (declare-const c Int)
    (assert (= z (+ (+ x y) c)))
    (assert (= x (- (- z y) c)))
    (assert (= y (- (- z x) c)))
    #end


The example realizes a fusion function for integer variables.  First, the variables x,y,z are declared. Variable c will be substituted by a random but fixed integer constant. Then fusion function :math:`z = f(x,y) =  x + y + c` is defined in the first assert block. Its corresponding inversion functions for x and y are described in the second and third asserts.     
