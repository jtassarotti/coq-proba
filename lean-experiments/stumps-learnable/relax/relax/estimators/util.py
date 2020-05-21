# Copyright © 2020, Oracle and/or its affiliates. All rights reserved.

import torch
import numpy as np

def unpack(model_samples):
    keys = []
    values = []
    for key in model_samples:
        keys.append(key)
        values.append(model_samples[key].numpy())
    return (keys,values)

def pack(keys,est_samples):
    model_samples = {}
    for i in range(len(keys)):
        model_samples[keys[i]] = torch.from_numpy(est_samples[i])
    return model_samples

def squeeze(x):
            if x < 0.:
                return 0.0001
            elif x > 1.:
                return 0.9999
            else:
                return x

vec_squeeze = np.vectorize(squeeze)
