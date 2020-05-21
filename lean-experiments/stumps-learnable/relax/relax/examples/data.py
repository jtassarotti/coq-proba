# Copyright © 2020, Oracle and/or its affiliates. All rights reserved.

##

female_accept = [{'gender': 'female', 'decision': 'accept'}]
male_accept = [{'gender': 'male', 'decision': 'accept'}]
female_reject = [{'gender': 'female', 'decision': 'reject'}]
male_reject = [{'gender': 'male', 'decision': 'reject'}]

data1 = female_accept * 5 + male_accept * 9 + female_reject * 40 + male_reject * 30

##

female_accept_qualified = [{'qualified': 'y', 'gender': 'female', 'decision': 'accept'}]
male_accept_qualified = [{'qualified': 'y','gender': 'male', 'decision': 'accept'}]
female_reject_qualified = [{'qualified': 'y','gender': 'female', 'decision': 'reject'}]
male_reject_qualified = [{'qualified': 'y','gender': 'male', 'decision': 'reject'}]
female_accept_unqualified = [{'qualified': 'n', 'gender': 'female', 'decision': 'accept'}]
male_accept_unqualified = [{'qualified': 'n','gender': 'male', 'decision': 'accept'}]
female_reject_unqualified = [{'qualified': 'n','gender': 'female', 'decision': 'reject'}]
male_reject_unqualified = [{'qualified': 'n','gender': 'male', 'decision': 'reject'}]

data2 = female_accept_qualified * 5 + male_accept_qualified * 9 + female_reject_qualified * 40 + male_reject_qualified * 30 + female_accept_unqualified * 1 + male_accept_unqualified * 5 + female_reject_unqualified * 9 + male_reject_unqualified * 9
