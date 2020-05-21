# Copyright © 2020, Oracle and/or its affiliates. All rights reserved.

from relax.estimators.BayesFactor import BFEstimator

class ISEstimator(BFEstimator):

    def null_proposal(self,num_samples):
        pass

    def alt_proposal(self,num_samples):
        pass
    
    def descriptor(self):
        return 'Importance Sampling'

    def estimate(self,num_samples,bf):
        (samples_0,is_probs_0) = self.null_proposal(num_samples)
        model_0 = bf.null_model.model_log_prob(samples_0,num_samples)

        (samples_a,is_probs_a) = self.alt_proposal(num_samples)     
        model_a = bf.alt_model.model_log_prob(samples_a,num_samples)

        probs_0 = model_0 - is_probs_0
        probs_a = model_a - is_probs_a

        return self.MC_BF_integrator(num_samples, probs_0, probs_a)
