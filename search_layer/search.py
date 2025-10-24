''' this class will contain the whole logic and workflow step by step  '''
import sys
import os

sys.path.append(os.path.join(os.path.dirname(__file__) , '..'))
from llm_layer.data_structures.base import LeanGoalState , SearchConstraints , TacticCandidate

class Search:
    def __init__(self):
        ...
    
    def search():
        # dfs for now>
        # candidates -> goal
        candidates = TacticCandidate

        for i,candidate in enumerate(candidates):
            # call validator
            ...
            # create new proof state?
