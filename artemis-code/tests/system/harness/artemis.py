
import os
import shutil
import subprocess

ARTEMIS_EXEC = 'artemis'
OUTPUT_DIR = '.output'

def execute_artemis(execution_uuid, url, iterations=1):

    output_dir = os.path.join(OUTPUT_DIR, execution_uuid)

    if os.path.isdir(output_dir):
        shutil.rmtree(output_dir)
        
    os.makedirs(output_dir)
    
    cmd = [ARTEMIS_EXEC, 
            "-i %s" % iterations,
            url] 

    stdout = subprocess.check_output(cmd, cwd=output_dir)

    fp = open(os.path.join(output_dir, 'stdout.txt'), 'w')
    fp.write(stdout)
    fp.close()