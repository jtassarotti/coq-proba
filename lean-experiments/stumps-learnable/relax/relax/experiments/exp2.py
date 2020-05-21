# Copyright © 2020, Oracle and/or its affiliates. All rights reserved.

import torch
import BFs
from experiment import *
from Models import *
from Estimators import *

const = {'N_0': 300, 'M_0': 300,
         'N_1': 300, 'M_1': 300,
         'alpha_0': 1.0, 'beta_0': 1.0,
         'alpha_1': 1.0, 'beta_1': 1.0}

null_model = BFs.equality_odds('_',const)
print_variables(null_model)

alt_model = BFs.equality_odds_dual('_',const)
print_variables(alt_model)

data = {'X_0': torch.tensor([7.]),
        'Y_0': torch.tensor([7.]),
        'X_1': torch.tensor([7.]),
        'Y_1': torch.tensor([7.])}

data_stan = {'X_0': 7,
             'Y_0': 7,
             'X_1': 7,
             'Y_1': 7}

test_equality_odds = BayesFactor(null_model,alt_model,data)

test_equality_odds.typ()

e_simple = [SimpleEstimator()]
#e_is = [KDEISEstimator(100,test_equality_odds)]
#e_pymc = [PYMC3KDEISEstimator(200,test_equality_odds,const,data)]
#e_stan = [PYSTANKDEISEstimator(200,test_equality_odds,const,data_stan)]
e_experiment = [Experiment(100,test_equality_odds,const,data_stan)]

estimators =  e_simple + e_experiment # + e_pymc + e_stan
num_samples = [get(6),get(4),get(4)]

experiment(estimators,num_samples,test_equality_odds)
