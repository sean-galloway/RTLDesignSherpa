python $REPO_ROOT/bin/pytree.py --path ./bridge/              --exclude-dir __pycache__ local_sim_build logs > bridge_tree.txt 
python $REPO_ROOT/bin/pytree.py --path ./converters/          --exclude-dir __pycache__ local_sim_build logs > converters_tree.txt
python $REPO_ROOT/bin/pytree.py --path ./retro_legacy_blocks/ --exclude-dir __pycache__ local_sim_build logs > rlb_tree.txt
python $REPO_ROOT/bin/pytree.py --path ./stream/              --exclude-dir __pycache__ local_sim_build logs > stream_tree.txt

