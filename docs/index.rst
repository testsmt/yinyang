yinyang: a fuzzer for SMT solvers 
====================================

.. figure:: ../media/logo.png
  :width: 90
  :align: center 


yinyang is a `fuzzer <https://en.wikipedia.org/wiki/Fuzzing>`_ for SMT solvers. Given a set of `SMT-LIB <http://smtlib.cs.uiowa.edu/language.shtml>`_ seed formulas, it generates mutant formulas which are then used as the test seeds for SMT solvers. yinyang roughly operates in the following stages: 


1. *Parsing:* First, yinyang parses a single or a set of SMT-LIB formulas to be used for fuzzing. yinyang comes with its own parser which is customizable and supports the SMT-LIB v2.6 standard. 

2. *Mutation:* Next, yinyang will mutate the parsed formula(s) using a mutation strategy. By default, yinyang performs type-aware substitutions of operators and will by default generate 300 mutant formulas per parsed formula.    

3. *Oracle Check:* Finally, yinyang will query the SMT solvers under test with the mutant formulas and compare the result against a test oracle. By default, such test oracle would be a second SMT solver. 

yinyang is intended for use by (1) SMT solver developers testing existing solvers, (2) researchers inventing new decision procedures to test the robustness of their implementations and (3) practitioners developing applications based on SMT solvers.    

.. toctree::
   :maxdepth: 2
 
   installation     
   setup
   basic_usage
   customization    
   fusion 
   building_on
