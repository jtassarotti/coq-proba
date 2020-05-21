import numpy as np
from scipy.stats import gaussian_kde

from relax.estimators.importance.ImportanceSampling import ISEstimator
from relax.estimators.util import *

class KDEISEstimator(ISEstimator):

    num_samples_IS = 100
    
    def __init__(self,num_samples,bf):
        self.num_samples_IS = num_samples
        self.null_proposal = self.proposal(bf.null_model)
        self.alt_proposal = self.proposal(bf.alt_model)
        
    def descriptor(self):
        return 'Gaussian KDE Importance Sampling ' + str(self.num_samples_IS)

    def proposal(self,model):
        
        vals = model.draw_posterior_samples(self.num_samples_IS)
        (keys,vals) = unpack(vals)

        values = np.array(vals)
        kernel = gaussian_kde(values)

        def sample_proposal(num_samples):
        
            proposals = kernel.resample(size=num_samples)
            proposals = vec_squeeze(proposals)
            probs = kernel.logpdf(proposals)
            proposals = pack(keys,proposals)
        
            return [proposals,probs]

        return sample_proposal
