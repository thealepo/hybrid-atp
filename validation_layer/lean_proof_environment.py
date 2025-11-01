import subprocess

class ProofEnvironment:
    def __init__(self , lean_execute: str = 'lean'):
        self.lean_execute = lean_execute

    def proof_check(self , file_path):
        # run lean on filepath
        try:
            result = subprocess.run(
                [self.lean_execute , file_path],
                check=True,
                capture_output=True,
                text=True
            )
            return True , result.stderr
        except subprocess.CalledProcessError as e:
            return False , e.stderr