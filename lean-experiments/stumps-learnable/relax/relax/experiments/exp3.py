# Copyright © 2020, Oracle and/or its affiliates. All rights reserved.

import torch
import BFs
from experiment import *
from Models import *
from Estimators import *

const = {}

for competence in ['_0','_1']:
    for gender in ['_male', '_female']:
        for age in ['_below40','_above40']:
            const['alpha' + gender + age + competence] = 1.0
            const['beta' + gender + age + competence] = 1.0
            const['N' + gender + age + competence] = 100
            const['M' + gender + age + competence] = 100
        
null_model = BFs.gm_aware(BFs.equality_odds,'_',const)
print_variables(null_model)

alt_model  = BFs.gm_aware(BFs.equality_odds_dual,'_',const)
print_variables(alt_model)

data = {}
data_stan = {}

for gender in ['_male', '_female']:
    for age in ['_below40','_above40']:
        for competence in ['_0','_1']:
            data['X' + gender + age + competence] = torch.tensor([20.])
            data['Y' + gender + age + competence] = torch.tensor([20.])
            data_stan['X' + gender + age + competence] = 20
            data_stan['Y' + gender + age + competence] = 20

test_gerry = BayesFactor(null_model,alt_model,data)

test_gerry.typ()

e_simple = [SimpleEstimator()]
#e_pyro = [KDEISEstimator(200,test_gerry)]
#e_pymc = [PYMC3KDEISEstimator(200,test_gerry,const,data)]
#e_stan = [PYSTANKDEISEstimator(200,test_gerry,const,data_stan)]
e_experiment = [Experiment(100,test_gerry,const,data_stan)]

estimators =  e_simple + e_experiment #+ e_pymc + e_stan #+ e_pyro
num_samples = [get(5),get(4),get(4),get(4)]

experiment(estimators,num_samples,test_gerry)
