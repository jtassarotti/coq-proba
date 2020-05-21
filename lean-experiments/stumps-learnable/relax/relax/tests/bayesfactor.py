# Copyright © 2020, Oracle and/or its affiliates. All rights reserved.

import torch
from relax.library.fairness import *
from relax.experiments.experiment import *
from relax.interface import *
from relax.estimators.Simple import *

const = {'N': 10, 'M': 10, 'alpha': 1.0, 'beta': 1.0}

null_model = demographic_parity('',const)
print_variables(null_model)

# Test 1

data = {'X': torch.tensor([7.]),'Y': torch.tensor([5.])}

test_demographic_parity = BayesFactor(null_model,null_model,data,fmap)

test_demographic_parity.typ()

e_simple = [SimpleEstimator()]

estimators = e_simple 
num_samples = [[100000]]

print('Mean should be close to 1.0')
experiment(estimators,num_samples,test_demographic_parity)

# Test 2

alt_model = demographic_parity_dual('',const)
print_variables(alt_model)

data = {'X': torch.tensor([7.]),'Y': torch.tensor([7.])}

test_demographic_parity = BayesFactor(null_model,alt_model,data,fmap)

test_demographic_parity.typ()

e_simple = [SimpleEstimator()]

estimators = e_simple 
num_samples = [[100000]]

print('Should be lower than 1.0')
experiment(estimators,num_samples,test_demographic_parity)

# Test 3

alt_model = demographic_parity_dual('',const)
print_variables(alt_model)

data = {'X': torch.tensor([7.]),'Y': torch.tensor([4.])}

test_demographic_parity = BayesFactor(null_model,alt_model,data,fmap)

test_demographic_parity.typ()

e_simple = [SimpleEstimator()]

estimators = e_simple 
num_samples = [[100000]]

print('Should be greater than 1.0')
experiment(estimators,num_samples,test_demographic_parity)
