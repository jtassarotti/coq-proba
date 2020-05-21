# Copyright © 2020, Oracle and/or its affiliates. All rights reserved.

import numpy as np

from relax.estimators.bridge.BridgeSampling import MengWongEstimator

class Harmonic(MengWongEstimator):

    def __init__(self,bf):
        self.null_proposal = bf.null_model.draw_posterior_samples
        self.alt_proposal = bf.alt_model.draw_posterior_samples
    
    def alpha(self,samples,num_samples):
        return np.zeros(num_samples)
