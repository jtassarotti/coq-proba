# Copyright © 2020, Oracle and/or its affiliates. All rights reserved.

import torch
import BFs
from experiment import *
from Models import *
from Estimators import *

const = {}

for i in ['gender','age']:
    const['N' + i + '0'] = 100. 
    const['M' + i + '0'] = 100.
    const['N' + i + '1'] = 100.
    const['M' + i + '1'] = 100.
    for j in ['0','1']:
        const['alpha' + i + j] = 1.0
        const['beta' + i + j] = 1.0


        
null_model = BFs.gm_oblivious(BFs.equality_odds,'',const)
print_variables(null_model)

alt_model = BFs.gm_oblivious(BFs.equality_odds_dual,'',const)
print_variables(alt_model)

data = {'Xgender0': torch.tensor([20.]),
        'Ygender0': torch.tensor([20.]),
        'Xage0': torch.tensor([20.]),
        'Yage0': torch.tensor([20.]),
        'Xgender1': torch.tensor([90.]),
        'Ygender1': torch.tensor([90.]),
        'Xage1': torch.tensor([90.]),
        'Yage1': torch.tensor([90.])}

test_gerry = BayesFactor(null_model,alt_model,data)

e_simple = [SimpleEstimator()]
#e_is = [KDEISEstimator(100,test_gerry)]

estimators =  e_simple #+ e_is 
num_samples = [get(5),get(5)]

experiment(estimators,num_samples,test_gerry)
