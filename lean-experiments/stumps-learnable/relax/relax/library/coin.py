# Copyright © 2020, Oracle and/or its affiliates. All rights reserved.

from relax import *

def coin_flip(path,const):
    def cf():
        mu = sample('mu' + path, Uniform(const['low' + path],const['high' + path]))
        k = sample('k' + path, Binomial(const['N' + path],mu))
        return [mu,k]
    return cf
