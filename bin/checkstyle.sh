#! /bin/bash
flake8  --exclude "*SMTLIBv2*,*runtests.py*,__init__.py" yinyang/src tests yinyang/config bin/opfuzz bin/yinyang bin/typefuzz --select=E --ignore=E402 --statistics 
