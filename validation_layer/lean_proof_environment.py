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
            print(f'6: {result}')
            success = (result.returncode == 0)
            print(f'7: {success}')
            return success, result.stderr
        except subprocess.CalledProcessError as e:
            print(f'6. {e}')
            print(f'{e.stderr}')
            print(f'{e.stdout}')
            return False, e.stderr