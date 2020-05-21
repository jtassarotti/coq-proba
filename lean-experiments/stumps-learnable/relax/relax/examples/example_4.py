# Copyright © 2020, Oracle and/or its affiliates. All rights reserved.

from relax import *
import relax.lean as lean

def coin_flip(path,const):
    def cf():
        mu = sample('mu' + path, Uniform(const['low' + path],const['high' + path]))
        k = sample('k' + path, Binomial(const['N' + path],mu))
        return [mu,k]
    return cf

const = {'N_': 1, 'low_': 0.0, 'high_': 1.0}

#lean.translate(coin_flip,const)

def coin_flip2(path,const):
    def cf():
        mu = sample('mu' + path, Uniform(const['low' + path],const['high' + path]))
        k1 = sample('k1' + path, Binomial(const['N' + path],mu))
        k2 = sample('k2' + path, Binomial(const['N' + path],mu))
        return [mu,k1,k2]
    return cf

const = {'N_': 1, 'low_': 0.0, 'high_': 1.0}

lean.translate(coin_flip2,const)
