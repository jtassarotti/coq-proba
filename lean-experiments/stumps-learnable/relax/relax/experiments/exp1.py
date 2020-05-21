# Copyright © 2020, Oracle and/or its affiliates. All rights reserved.

import torch
from relax.interface import BayesFactor, print_variables
from relax.library.fairness import *
from relax.experiments.experiment import *

import relax.estimators.Simple as simple
import relax.estimators.importance.KDE as KDE
import relax.estimators.bridge.harmonic as harmonic
import relax.estimators.importance.KDE_tips as Stan

const = {'N': 400, 'M': 400, 'alpha': 1.0, 'beta': 1.0}

null_model = demographic_parity('',const)
print_variables(null_model)

alt_model = demographic_parity_dual('',const)
print_variables(alt_model)

data = {'X': torch.tensor([7.0]),'Y': torch.tensor([5.0])}
data_stan = {'X': 7,'Y': 5}

test_demographic_parity = BayesFactor(null_model,alt_model,data,fmap)

test_demographic_parity.typ()

e_simple = [simple.SimpleEstimator()]
e_is = [KDE.KDEISEstimator(100,test_demographic_parity)]
#e_harmonic = [harmonic.Harmonic(test_demographic_parity)]
e_experiment = [Stan.Experiment(100,test_demographic_parity,const,data_stan)]

estimators = e_simple + e_is + e_experiment
num_samples = [get(6),get(4),get(4),get(4)]

experiment(estimators,num_samples,test_demographic_parity)
