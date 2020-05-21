# Copyright © 2020, Oracle and/or its affiliates. All rights reserved.

import numpy as np
from scipy.special import logsumexp

class BFEstimator():

    def descriptor(self):
        pass

    def estimate(self,num_samples,bf):
        pass

    def MC_BF_integrator(self,num_samples, log_p_0, log_p_a):
    
        ev_0 = logsumexp(log_p_0) - np.log(num_samples)
        ev_a = logsumexp(log_p_a) - np.log(num_samples)        
        bf = np.exp(ev_a - ev_0)

        return bf
