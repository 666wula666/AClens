import re
import subprocess
import logging
import os
from pathlib import Path

logger = logging.getLogger("ACLens")

class SolcManager:
    @staticmethod
    def extract_version(file_path: str) -> str:
        """
        Extracts the exact Solidity version from the pragma statement.
        Example: 'pragma solidity ^0.8.0;' -> '0.8.0' (simplified)
        
        It handles:
        - ^0.8.0 -> 0.8.0 (Use the lowest compatible or just the version number)
        - >=0.7.0 <0.9.0 -> 0.7.0
        - 0.4.26 -> 0.4.26
        """
        if not os.path.exists(file_path):
            return None

        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            # Regex for pragma solidity
            # Matches: pragma solidity ^0.8.0; or pragma solidity 0.8.0;
            match = re.search(r'pragma\s+solidity\s+([^;]+);', content)
            if match:
                version_str = match.group(1).strip()
                
                # Simple heuristic: extract the first version number found
                # This covers ^0.8.0, >=0.8.0, 0.8.0
                v_match = re.search(r'(\d+\.\d+\.\d+)', version_str)
                if v_match:
                    return v_match.group(1)
        except Exception as e:
            logger.warning(f"Failed to extract solc version: {e}")
        
        return None

    @staticmethod
    def install_and_use(version: str):
        """
        Switch to an already-installed solc version via solc-select.

        This method intentionally avoids forcing a local VIRTUAL_ENV or
        downloading compilers at runtime. In reproducible experiment
        environments, the required solc versions should already exist
        in the user's solc-select artifact store.
        """
        if not version:
            logger.warning("No solc version specified to switch.")
            return

        logger.info(f"Attempting to switch solc to version {version}...")

        try:
            env = os.environ.copy()

            # Do not let an unrelated virtualenv redirect solc-select to a
            # different artifact directory.
            env.pop("VIRTUAL_ENV", None)
            os.environ.pop("VIRTUAL_ENV", None)

            # Prefer the explicit environment variable because subprocesses
            # launched later in the same Python process will read it directly.
            os.environ["SOLC_VERSION"] = version
            env["SOLC_VERSION"] = version

            # Keep the global-version file aligned for interactive debugging
            # and shell-based verification outside this process.
            subprocess.run(
                ["solc-select", "use", version],
                check=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                env=env,
            )

            artifacts_dir = Path.home() / ".solc-select" / "artifacts" / f"solc-{version}" / f"solc-{version}"
            if not artifacts_dir.exists():
                raise FileNotFoundError(
                    f"solc {version} is not installed under {artifacts_dir}. "
                    f"Please install it first with `solc-select install {version}`."
                )

            check_res = subprocess.run(
                ["solc", "--version"],
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                env=env,
                text=True,
                check=True,
            )
            version_output = check_res.stdout.strip().splitlines()
            if len(version_output) >= 2:
                logger.info(f"Successfully configured solc: {version_output[1]}")
            else:
                logger.info(f"Successfully configured solc: {check_res.stdout.strip()}")
        except FileNotFoundError:
            logger.error("solc-select not found. Please install it: pip3 install solc-select")
        except subprocess.CalledProcessError as e:
            err_msg = e.stderr if isinstance(e.stderr, str) else (e.stderr.decode() if e.stderr else str(e))
            logger.error(f"Failed to switch solc version: {err_msg}")
        except Exception as e:
            logger.error(f"Unexpected error in solc switching: {e}")
