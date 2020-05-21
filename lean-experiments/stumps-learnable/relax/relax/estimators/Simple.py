# Copyright © 2020, Oracle and/or its affiliates. All rights reserved.

from relax.estimators.BayesFactor import BFEstimator

class SimpleEstimator(BFEstimator):

    def descriptor(self):
        return 'MC Integration'
    
    def estimate(self,num_samples,bf):
        null_samples = bf.null_model.draw_prior_samples(num_samples)
        null_probs = bf.null_model.likelihood_log_prob(null_samples,num_samples)
        
        alt_samples = bf.alt_model.draw_prior_samples(num_samples)
        alt_probs = bf.alt_model.likelihood_log_prob(alt_samples,num_samples)
        
        return self.MC_BF_integrator(num_samples, null_probs, alt_probs)
