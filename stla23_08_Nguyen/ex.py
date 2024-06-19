from sklearn.datasets import load_breast_cancer
from sklearn.model_selection import train_test_split
from sklearn.naive_bayes import GaussianNB
from sklearn.tree import DecisionTreeClassifier
from sklearn.svm import SVC
from sklearn.neighbors import KNeighborsClassifier
from sklearn.metrics import accuracy_score, f1_score


breast_cancer_data = load_breast_cancer()
X_bc = breast_cancer_data.data
y_bc = breast_cancer_data.target


X_bc_train, X_bc_test, y_bc_train, y_bc_test = train_test_split(X_bc, y_bc, test_size=0.2, random_state=0)


def evaluate_breast_cancer_models():
    models = [GaussianNB(), DecisionTreeClassifier(), SVC(), KNeighborsClassifier()]

    for model in models:
        model.fit(X_bc_train, y_bc_train)
        y_pred = model.predict(X_bc_test)
        
        acc = accuracy_score(y_bc_test, y_pred)
        f1 = f1_score(y_bc_test, y_pred, average='weighted')
        
        print(f"Model: {model.__class__.__name__}, Accuracy: {acc:.4f}, F1-score: {f1:.4f}")

evaluate_breast_cancer_models()



from sklearn.datasets import fetch_covtype

data = fetch_covtype()
target = data['target'][np.logical_or(data['target'] == 2, data['target'] == 3)] - 2
data = data['data'][np.logical_or(data['target'] == 2, data['target'] == 3)]


X_ct_train, X_ct_test, y_ct_train, y_ct_test = train_test_split(data, target, test_size=0.2, random_state=0)


def evaluate_cover_type_models():
    models = [GaussianNB(), DecisionTreeClassifier(), SVC(), KNeighborsClassifier()]

    for model in models:
        model.fit(X_ct_train, y_ct_train)
        y_pred = model.predict(X_ct_test)
        
        acc = accuracy_score(y_ct_test, y_pred)
        f1 = f1_score(y_ct_test, y_pred, average='weighted')
        
        print(f"Model: {model.__class__.__name__}, Accuracy: {acc:.4f}, F1-score: {f1:.4f}")


evaluate_cover_type_models()