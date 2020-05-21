# Copyright © 2020, Oracle and/or its affiliates. All rights reserved.

from relax import *

def majority(path, const):
    
    pro_tip = ('STAN_NUTS',['theta' + path], ['X' + path])
    
    def inner():
        theta  = sample('theta' + path, Beta(const['alpha' + path],const['beta' + path]))
        X = sample('X' + path, Binomial(const['N' + path],theta))
        pro_tip
        return [theta,X]
    
    return inner

def demographic_parity(path,const):

    pro_tip = ('STAN_NUTS', ['theta' + path, 'phi' + path], ['X' + path, 'Y' + path])
    
    def dmp():
        [theta,X] = majority(path,const)()
        phi  = sample('phi' + path, Uniform(0.8 * theta,1.0))
        Y = sample('Y' + path, Binomial(const['M' + path],phi))
        pro_tip
        return [phi,Y]
    return dmp

def demographic_parity_dual(path,const):

    pro_tip = ('STAN_NUTS', ['theta' + path, 'phi' + path], ['X' + path, 'Y' + path])
    
    def dmpd():
        [theta,X] = majority(path,const)()
        phi  = sample('phi' + path, Uniform(0.0,theta * 0.8))
        Y = sample('Y' + path, Binomial(const['M' + path],phi))
        pro_tip
        return [phi,Y]
    
    return dmpd

def demographic_parity_oblivious(path,const):

    pro_tip = ('Block',['theta' + path,'X' + path],['phi' + path,'Y' + path])
    
    def dmo():
        [theta,X] = majority(path,const)()
        phi  = sample('phi' + path, Beta(const['alphao' + path],const['betao' + path]))
        Y = sample('Y' + path, Binomial(const['M' + path],phi))
        pro_tip
        return [phi,Y]
    
    return dmo

def equality_odds_simple(path,const):
    def eot():
        for j in ['0','1']:
            demographic_parity(path + j,const)()        
    return eot

def equality_odds_template(f,path,const):

    pro_tip = ('Block', [path + '0', path + '1'])
    
    def eot():
        for j in ['0','1']:
            f(path + j,const)()
        pro_tip
        
    return eot

def equality_odds(path,const):
    def eo():
        equality_odds_template(demographic_parity,path,const)()  
    return eo

def equality_odds_dual(path,const):
    def eod():
        equality_odds_template(demographic_parity_dual,path,const)()  
    return eod

def gm_oblivious(f,path,const):
    def gmo():
        f(path + 'gender',const)()
        f(path + 'age' ,const)()
    return gmo

def gm_aware(f,path,const):
    def gma():
        for j in ['female_','male_']:
            for k in ['below40_','above40_']:
                f(path + j + k,const)()
    return gma



