#! python3
from sklearn import tree
import random
import pickle

random.seed(42)

with open("./out_stats_all") as f:
    b =[ i for i in  f.readlines() if (i.startswith("Checking") and "time" in i) or any([i.startswith(j) for j in ["Z3_bindings:", "Z3:", "CVC4", "Yices", "Boolector", "BitWuzla"]])]


#print "All queries: ", len(b)
c = [[j for j in map(lambda x: x.strip(), i.split(":"))] for i in b]
d = dict()

for i in c:                             
    if i[0] in d:
        d[i[0]].append({'x': [j for j in map(int,i[1:-1])], 'y': float(i[-1])})
    else:
        d[i[0]] = [{'x': [j for j in map(int,i[1:-1])], 'y': float(i[-1])}]

train_per = 0.7
error_margin = 1.
clf = dict()
for i in d:
    clf[i] = tree.DecisionTreeRegressor()
    data_target = [(d['x'],d['y']) for d in d[i]]
    random.shuffle(data_target)
    data, target = zip(*data_target)
    num_train = int(0.7*len(data))
    train_data = data[:num_train]
    train_target = target[:num_train]


    clf[i].fit(train_data,train_target)
    
    test_data = data[num_train:]
    test_target = target[num_train:]
    pred_target = clf[i].predict(test_data)

    for j,k in zip(test_target,pred_target):
        if j>1.:
            k2 = k/j
            j2 = 1.
        else:
            j2,k2 = j, k
            
        if abs(j2-k2) > error_margin:
            print ( i, j, k, j2, k2, j-k )
    pickle.dump(clf[i], open("pred_%s.pickle"%i, "wb"))
    
pickle.dump(clf, open("regressors.pickle", "wb"))

