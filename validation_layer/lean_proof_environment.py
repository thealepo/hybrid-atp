import subprocess

class ProofEnvironment:
    def __init__(self , lean_execute: str = "lake"):
        self.lean_execute = lean_execute

    def proof_check(self , file_path: str , project_root: str):
        try:
            result = subprocess.run(
                [self.lean_execute , 'build'],
                capture_output=True,
                text=True,
                check=True,
                cwd=project_root
            )
            success = (result.returncode == 0)
            return success, result.stderr
        except subprocess.CalledProcessError as e:
            return False, e.stderr