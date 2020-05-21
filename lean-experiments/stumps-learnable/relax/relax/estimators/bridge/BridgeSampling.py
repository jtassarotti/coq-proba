# Copyright © 2020, Oracle and/or its affiliates. All rights reserved.

from relax.estimators.BayesFactor import BFEstimator

class MengWongEstimator(BFEstimator):

    # Must be posterior samples
    def null_proposal(self,num_samples):
        pass

    # Must be posterior samples
    def alt_proposal(self,num_samples):
        pass

    def alpha(self,samples,num_samples):
        pass
    
    def descriptor(self):
        return 'Meng Wong Sampling'
    
    def estimate(self,num_samples, bf):

        samples_0 = self.null_proposal(num_samples)
        model_a = bf.alt_model.model_log_prob(samples_0,num_samples)
        alpha_a = self.alpha(samples_0, num_samples)
        
        samples_a = self.alt_proposal(num_samples)     
        model_0 = bf.null_model.model_log_prob(samples_a,num_samples)
        alpha_0 = self.alpha(samples_a, num_samples)
        
        probs_0 = model_0 + alpha_0
        probs_a = model_a + alpha_a

        return self.MC_BF_integrator(num_samples, probs_0 , probs_a )
