import subprocess

class ProofEnvironment:
    def __init__(self, lean_execute: str = "lean"):
        self.lean_execute = lean_execute

    def proof_check(self, file_path):
        try:
            # debugging
            print('\n\n\n\n')
            print('THIS IS THE COMMAND THAT IS BEING PASSED')
            print(''.join(self.lean_execute))
            print('\n\n\n\n')
            # ----------------------
            result = subprocess.run(
                [self.lean_execute, file_path],
                capture_output=True,
                text=True,
                check=True
            )
            print(f'6: {result}')
            success = (result.returncode == 0)
            print(f'7: {success}')
            return success, result.stderr
        except subprocess.CalledProcessError as e:
            return False, e.stderr
