# Copyright © 2020, Oracle and/or its affiliates. All rights reserved.


import torch
import pyro.infer
from pyro.infer import MCMC, NUTS
import pyro.poutine as poutine
import pyro.poutine.indep_messenger as messenger
import inspect
import relax.vm

def get_rvs(model,observed):
        tr = poutine.trace(model).get_trace()
        params = []
        for key in tr.nodes:
            if tr.nodes[key]['type'] == 'sample' and tr.nodes[key]['is_observed'] == observed:
                params.append(key)
        return params

def print_variables(model):
      print(get_rvs(model,False))  

class Model():

    batch_size = 0
    parameters = []
    observed = []
    model = 0
    data = {}
    descriptor = 'Model'
    block_info = None
    stan_info = None
    
    def __init__(self,model,data,descriptor,block_info=None,stan_info=None):
        self.descriptor = descriptor
        self.model = poutine.condition(model, data=data)
        self.parameters = get_rvs(self.model,False)
        self.observed = get_rvs(self.model,True)
        self.data = data
        self.block_info = block_info
        self.stan_info = stan_info
        
    def typ(self):
        print('Model name: ', self.descriptor)
        print('Parameters: ', self.parameters)
        print('Observed: ', self.observed)

    def descriptor(self):
        return self.descriptor

    def draw_posterior_samples(self,num_samples):
        nuts_kernel = NUTS(self.model, adapt_step_size=True)
        mcmc = MCMC(nuts_kernel, num_samples=num_samples, warmup_steps=300)
        mcmc.run()
        res = mcmc.get_samples()
        return res

    def model_log_prob(self,samples,num_samples):
        ll = self.likelihood_log_prob(samples,num_samples)
        lp = self.prior_log_prob(samples,num_samples)
        return ll + lp 

    def likelihood_log_prob(self,samples,num_samples):
        @poutine.broadcast
        def model_bcast():
            with messenger.IndepMessenger("batch", num_samples):
                self.model()
        prior = poutine.block(model_bcast, hide_types=["observe"])
        prior_trace = poutine.trace(prior).get_trace()
        for rv in self.parameters:
            if (type(prior_trace.nodes[rv]['fn']) == pyro.poutine.subsample_messenger._Subsample):
                continue
            prior_trace.nodes[rv]['value'] = samples[rv]
        trace = poutine.trace(poutine.replay(model_bcast, trace=prior_trace)).get_trace()
        trace.compute_log_prob()
        log_probs = torch.zeros(num_samples)
        for rv in self.observed:
            if (type(trace.nodes[rv]['fn']) == pyro.poutine.subsample_messenger._Subsample):
                continue
            log_probs += trace.nodes[rv]['log_prob']
        return log_probs 
    
    def draw_prior_samples(self,num_samples):
        @poutine.broadcast
        def model_bcast():
            with messenger.IndepMessenger("batch", num_samples):
                self.model()
        prior = poutine.block(model_bcast, hide_types=["observe"])
        prior_trace = poutine.trace(prior).get_trace()
        mydict = {}
        for rv in self.parameters:
            if (type(prior_trace.nodes[rv]['fn']) == pyro.poutine.subsample_messenger._Subsample):
                continue
            mydict[rv] = prior_trace.nodes[rv]['value']
        return mydict

    def prior_log_prob(self,samples,num_samples):
        @poutine.broadcast
        def model_bcast():
            with messenger.IndepMessenger("batch", num_samples):
                self.model()
        prior = poutine.block(model_bcast, hide_types=["observe"])
        prior_trace = poutine.trace(prior).get_trace()
        for rv in self.parameters:
            if (type(prior_trace.nodes[rv]['fn']) == pyro.poutine.subsample_messenger._Subsample):
                continue
            prior_trace.nodes[rv]['value'] = samples[rv]
        trace = poutine.trace(poutine.replay(prior, trace=prior_trace)).get_trace()
        trace.compute_log_prob()
        log_probs = torch.zeros(num_samples)
        for rv in self.parameters:
            if (type(trace.nodes[rv]['fn']) == pyro.poutine.subsample_messenger._Subsample):
                continue
            log_probs += trace.nodes[rv]['log_prob']
        return log_probs

class BayesFactor:

    null_model = 0
    alt_model = 0
    desc = 'Bayes Factor'

    def __init__(self,null_model,alt_model,data):

        (rvmap,pro_tips) = relax.vm.concolic_vm(null_model)
        block_info = relax.vm.get_blocks(rvmap,pro_tips)
        stan_info = relax.vm.to_stan(rvmap,pro_tips)
        self.null_model = Model(null_model,data,null_model.__name__,block_info,stan_info)

        (rvmap,pro_tips) = relax.vm.concolic_vm(alt_model)
        block_info = relax.vm.get_blocks(rvmap,pro_tips)
        stan_info = relax.vm.to_stan(rvmap,pro_tips)
        self.alt_model = Model(alt_model,data,alt_model.__name__,block_info,stan_info)
        self.desc = null_model.__name__ + ' vs ' + alt_model.__name__
        
    def descriptor(self):
        return self.desc

    def typ(self):
        self.null_model.typ()
        self.alt_model.typ()
