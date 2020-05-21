# Copyright © 2020, Oracle and/or its affiliates. All rights reserved.

# In this example, we specify and estimate a Bayes Factor for the 4-5th rule

import torch
from relax import *
from relax.interface import BayesFactor
from relax.estimators.Simple import SimpleEstimator
from data import data2 as data

# Step 0: pre-process the data

candidates_qualified = filter(lambda candidate: candidate['qualified'] == 'y',data)
candidates_unqualified = filter(lambda candidate: candidate['qualified'] == 'n',data)

female_candidates_qualified = filter(lambda candidate: candidate['gender'] == 'female',candidates_qualified)
male_candidates_qualified = filter(lambda candidate: candidate['gender'] == 'male',candidates_qualified)
female_accepted_qualified = filter(lambda candidate: candidate['decision'] == 'accept',female_candidates_qualified)
male_accepted_qualified = filter(lambda candidate: candidate['decision'] == 'accept',male_candidates_qualified)

female_candidates_unqualified = filter(lambda candidate: candidate['gender'] == 'female',candidates_unqualified)
male_candidates_unqualified = filter(lambda candidate: candidate['gender'] == 'male',candidates_unqualified)
female_accepted_unqualified = filter(lambda candidate: candidate['decision'] == 'accept',female_candidates_unqualified)
male_accepted_unqualified = filter(lambda candidate: candidate['decision'] == 'accept',male_candidates_unqualified)

nfcq = len(list(female_candidates_qualified))
nmcq = len(list(male_candidates_qualified))
nfaq = len(list(female_accepted_qualified))
nmaq = len(list(male_accepted_qualified))

nfcu = len(list(female_candidates_unqualified))
nmcu = len(list(male_candidates_unqualified))
nfau = len(list(female_accepted_unqualified))
nmau = len(list(male_accepted_unqualified))

# Step 1: specify the models

def majority(path, const):
    
    def model():
        theta  = sample('theta' + path, Beta(const['alpha' + path],const['beta' + path]))
        X = sample('X' + path, Binomial(const['N' + path],theta))
        return [theta,X]
    
    return model

def minority(theta,path,const):

    def model():
        phi  = sample('phi' + path, Uniform(0.8 * theta,1.0))
        Y = sample('Y' + path, Binomial(const['M' + path],phi))
        return [phi,Y]
        
    return model

def demographic_parity(path,const):

    def model():
        [theta,X] = majority(path,const)()
        minority(theta,path,const)()

    return model

def demographic_parity_dual(path,const):

    def model():
        [theta,X] = majority(path,const)()
        phi  = sample('phi' + path, Uniform(0.0,0.8 * theta))
        Y = sample('Y' + path, Binomial(const['M' + path],phi))

    return model

def demographic_parity_oblivious(path,const):

    def model():
        majority(path,const)()
        phi  = sample('phi' + path, Beta(const['gamma' + path],const['delta' + path]))
        Y = sample('Y' + path, Binomial(const['M' + path],phi))

    return model

def equality_odds_template(f,path,const):

    def model():
        for j in ['qualified','unqualified']:
            f(path + j,const)()
        
    return model

# Step 2: create the Bayes Factor

constants = {'N_qualified': nmcq,
             'M_qualified': nfcq,
             'N_unqualified': nmcu,
             'M_unqualified': nfcu,
             'alpha_qualified': 1.0,
             'beta_qualified': 1.0,
             'alpha_unqualified': 1.0,
             'beta_unqualified': 1.0
}

data = {'X_qualified': torch.tensor([float(nmaq)]),
        'Y_qualified': torch.tensor([float(nfaq)]),
        'X_unqualified': torch.tensor([float(nmau)]),
        'Y_unqualified': torch.tensor([float(nfau)])
}

null_model = equality_odds_template(demographic_parity,'_',constants)

alternative_model_1 = equality_odds_template(demographic_parity_dual,'_',constants)
test_equality_odds_1 = BayesFactor(null_model,alternative_model_1,data)

constants.update({'gamma_qualified': 1.0,
                   'delta_qualified': 1.0,
                   'gamma_unqualified': 1.0,
                   'delta_unqualified': 1.0
                   })

alternative_model_2 = equality_odds_template(demographic_parity_oblivious,'_',constants)
test_equality_odds_2 = BayesFactor(null_model,alternative_model_2,data)


# Step 3: Estimation

estimator = SimpleEstimator()
estimation_1 = estimator.estimate(100000,test_equality_odds_1)
estimation_2 = estimator.estimate(100000,test_equality_odds_2)

print('Estimate of dual Bayes Factor: ', estimation_1)
print('Estimate of oblivious Bayes Factor: ', estimation_2)
