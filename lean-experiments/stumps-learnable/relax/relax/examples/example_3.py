# Copyright © 2020, Oracle and/or its affiliates. All rights reserved.

# In this example, we specify and estimate a Bayes Factor for the 4-5th rule

import torch
from relax import *
from relax.interface import BayesFactor
import relax.estimators.importance.KDE_tips as Stan
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

def demographic_parity(path,const):

    pro_tip = ('STAN_NUTS', ['theta' + path, 'phi' + path], ['X' + path, 'Y' + path])
    
    def model():
        [theta,X] = majority(path,const)()
        phi  = sample('phi' + path, Uniform(0.8 * theta,1.0))
        Y = sample('Y' + path, Binomial(const['M' + path],phi))
        pro_tip

    return model

def demographic_parity_dual(path,const):

    pro_tip = ('STAN_NUTS', ['theta' + path, 'phi' + path], ['X' + path, 'Y' + path])
    
    def model():
        [theta,X] = majority(path,const)()
        phi  = sample('phi' + path, Uniform(0.0,0.8 * theta))
        Y = sample('Y' + path, Binomial(const['M' + path],phi))
        pro_tip

    return model

def equality_odds_template(f,path,const):

    pro_tip = ('Block', [path + 'qualified', path + 'unqualified'])
    
    def model():
        for j in ['qualified','unqualified']:
            f(path + j,const)()
        pro_tip
        
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

data_stan = {'X_qualified': nmaq,
        'Y_qualified': nfaq,
        'X_unqualified': nmau,
        'Y_unqualified': nfau
}

null_model = equality_odds_template(demographic_parity,'_',constants)

alternative_model = equality_odds_template(demographic_parity_dual,'_',constants)
test_equality_odds = BayesFactor(null_model,alternative_model,data)

# Step 3: 

estimator = Stan.Experiment(100,test_equality_odds,constants,data_stan)
estimation = estimator.estimate(100000,test_equality_odds)

print('Estimate of dual Bayes Factor: ', estimation)

