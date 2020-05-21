# Copyright © 2020, Oracle and/or its affiliates. All rights reserved.

import numpy as np
import logging
import matplotlib.pyplot as plt

def experiment(estimators,num_samples,bayes_factor):

    repeat = 10
    
    results_mean_global = []
    results_variance_global = []
    
    for i in range(len(estimators)):

        results_mean_local = []
        results_variance_local = []
        
        print(estimators[i].descriptor(), flush=True)

        samples = num_samples[i]

        for j in range(len(samples)):
    
            bfs = np.zeros(repeat)
            
            for k in range(repeat):

                bf = estimators[i].estimate(samples[j],bayes_factor)
        
                bfs[k] = bf

            results_mean_local.append(np.mean(bfs))
            results_variance_local.append(np.var(bfs))

            print('Mean: ', np.mean(bfs))
            print('Variance: ', np.var(bfs))
            
        results_mean_global.append(results_mean_local)
        results_variance_global.append(results_variance_local)
                
            
    plt.axhline(y=0., color='cyan', linestyle='dashed')
    plt.yscale('symlog')
    plt.xscale('log')
    plt.title('Bayes Factor: ' + bayes_factor.descriptor())
    plt.xlabel('Log number of samples')
    plt.ylabel('Log variance')
        
    colors = ['red','green','blue','yellow','black']
    for i in range(len(estimators)):
        plt.plot(num_samples[i],results_variance_global[i],color=colors[i],label=estimators[i].descriptor())

    plt.legend(loc="upper right")
    plt.show()
    
def get(num):
    s = []
    for i in range(num):
        s.append(10**(i+1))
    return s






