import subprocess

class ProofEnvironment:
    def __init__(self , project_root: str):
        self.project_root = project_root

    def proof_check(self , file_path):
        # run lean on filepath
        try:
            # running Lean via lake
            result = subprocess.run(
                ['lake' , 'build' , '--fast'],
                cwd=self.project_root,
                capture_output=True,
                text=True
            )
            success = (result.returncode == 0)
            return success , result.stderr
        except subprocess.CalledProcessError as e:
            return False , e.stderr