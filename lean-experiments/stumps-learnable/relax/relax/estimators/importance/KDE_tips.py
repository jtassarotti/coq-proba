# Copyright © 2020, Oracle and/or its affiliates. All rights reserved.

import numpy as np
from scipy.stats import gaussian_kde
import pystan

from relax.estimators.importance.ImportanceSampling import ISEstimator
from relax.estimators.util import *

class Experiment(ISEstimator):

    num_samples_IS = 100
    const = 0
    data = 0
    
    def __init__(self,num_samples,bf,const,data):
        self.const = const
        self.data = data
        self.num_samples_IS = num_samples
        self.null_proposal = self.proposal(self.samples_dm,bf.null_model.parameters,bf.null_model.block_info,bf.null_model.stan_info)
        self.alt_proposal = self.proposal(self.samples_dm,bf.alt_model.parameters,bf.alt_model.block_info,bf.alt_model.stan_info)

    def descriptor(self):
        return 'Pro Tip Experimentation ' + str(self.num_samples_IS)

    thin = 10
    warmup = 300

    def samples_dm(self,num_samples,const,data,stan_model):
        data.update(const)
        iterations = num_samples * self.thin + self.warmup
        sm = pystan.StanModel(model_code=stan_model)
        fit = sm.sampling(data=data, iter=iterations, chains=4, warmup=self.warmup, thin=self.thin)
        keys = []
        result = []
        for key in fit.extract():
            if key != 'lp__':
                keys.append(key)
                result.append(np.array(fit[key]))
        return (keys,result)
    
    def proposal(self,f,parameters,blocks,stan_models):

        if blocks == []:
            blocks = [parameters]
            
        blocks = [list(filter(lambda x: x in parameters, block)) for block in blocks]

        # This absolutely needs to be replaced, the stan_models must expose what their parameters are
        stan_models.reverse()
                    
        N = len(blocks)

        kernels = {}
        keys = []
        
        for i in range(N):
                 
            (key,vals) = f(self.num_samples_IS,self.const,self.data,stan_models[i])        
            values = np.array(vals)
            
            ker = gaussian_kde(values)

            kernels[i] = ker
            keys.extend(key)
            
        def sample_proposal(num_samples):

            proposals = []
            probs = np.zeros(num_samples)
            
            for i in range(N):
            
                prop = kernels[i].resample(size=num_samples)
                prop = vec_squeeze(prop)
                probas = kernels[i].logpdf(prop)
                
                proposals.append(prop[0])
                proposals.append(prop[1])
                probs += probas

            proposals = np.array(proposals)
            #print(keys)
            #print(proposals)
            proposals = pack(keys,proposals)
            
            return [proposals,probs]

        return sample_proposal
