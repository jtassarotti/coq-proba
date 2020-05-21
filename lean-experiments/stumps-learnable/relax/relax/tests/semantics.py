# Copyright © 2020, Oracle and/or its affiliates. All rights reserved.

import inspect
from functools import partial
import ast
import astpretty
import parser
import _ast
import dis
import types

from BFs import *

import pyro
from pyro import sample
from pyro.distributions import *

from Semantics import *

exp = 5

const0 = {'N_': 100, 'low_': 0.0, 'high_': 1.0}

if exp == 0:
    to_lean(coin_flip,const0)

const = {'N_': 100, 'M_': 100, 'alpha_': 1.0, 'beta_': 1.0}
        
if exp == 1:
    run_and_print(majority('_',const),0)

if exp == 2:
    run_and_print(demographic_parity('_',const),0)

const2 = {'N_0': 300, 'M_0': 300,
         'N_1': 300, 'M_1': 300,
         'alpha_0': 1.0, 'beta_0': 1.0,
         'alpha_1': 1.0, 'beta_1': 1.0}
        
if exp == 3:
    run_and_print(equality_odds_simple('_',const2),0)

if exp == 4:
    run_and_print(equality_odds('_',const2),0)

const3 = {}

for competence in ['_0','_1']:
    for gender in ['_male', '_female']:
        for age in ['_below40','_above40']:
            const3['alpha' + gender + age + competence] = 1.0
            const3['beta' + gender + age + competence] = 1.0
            const3['N' + gender + age + competence] = 100.0
            const3['M' + gender + age + competence] = 100.0
        
if exp == 5:
    my_model = gm_aware(equality_odds,'_',const3)
    run_and_print(my_model,0)

if exp == 6:
    to_stan(demographic_parity,const)

