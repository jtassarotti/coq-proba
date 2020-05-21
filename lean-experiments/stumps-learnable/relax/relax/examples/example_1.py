# Copyright © 2020, Oracle and/or its affiliates. All rights reserved.

# In this example, we specify and estimate a Bayes Factor for the 4-5th rule

import torch
from relax import *
from relax.interface import BayesFactor
from relax.estimators.Simple import SimpleEstimator
from data import data1 as data

# Step 0: pre-process the data

female_candidates = filter(lambda candidate: candidate['gender'] == 'female',data)
male_candidates = filter(lambda candidate: candidate['gender'] == 'male',data)
female_accepted = filter(lambda candidate: candidate['decision'] == 'accept',female_candidates)
male_accepted = filter(lambda candidate: candidate['decision'] == 'accept',male_candidates)

nfc = len(list(female_candidates))
nmc = len(list(male_candidates))
nfa = len(list(female_accepted))
nma = len(list(male_accepted))

# Step 1: specify two models: null and alternative

def demographic_parity(path,const):

    def model():
        theta  = sample('theta', Beta(const['alpha'],const['beta']))
        X = sample('X', Binomial(const['N'],theta))
        phi  = sample('phi', Uniform(0.8 * theta,1.0))
        Y = sample('Y', Binomial(const['M'],phi))

    return model

def demographic_parity_dual(path,const):

    def model():
        theta  = sample('theta', Beta(const['alpha'],const['beta']))
        X = sample('X', Binomial(const['N'],theta))
        phi  = sample('phi', Uniform(0.0,0.8 * theta))
        Y = sample('Y', Binomial(const['M'],phi))

    return model

# Step 2: create the Bayes Factor

constants = {'N': nmc, 'M': nfc, 'alpha': 1.0, 'beta': 1.0}
data = {'X': torch.tensor([float(nma)]),'Y': torch.tensor([float(nfa)])}

null_model = demographic_parity('',constants)
alternative_model = demographic_parity_dual('',constants)
test_demographic_parity = BayesFactor(null_model,alternative_model,data)

# Step 3: estimate the Bayes factor

estimator = SimpleEstimator()
estimation = estimator.estimate(100000,test_demographic_parity)

print('Estimate of Bayes Factor: ', estimation)
