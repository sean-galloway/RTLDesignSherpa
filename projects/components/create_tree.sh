python $REPO_ROOT/bin/pytree.py --path ./apb_xbar/            --exclude-dir __pycache__ local_sim_build logs > apb_xbar_tree.txt 
python $REPO_ROOT/bin/pytree.py --path ./bridge/              --exclude-dir __pycache__ local_sim_build logs > bridge_tree.txt 
python $REPO_ROOT/bin/pytree.py --path ./converters/          --exclude-dir __pycache__ local_sim_build logs > converters_tree.txt
python $REPO_ROOT/bin/pytree.py --path ./misc/                --exclude-dir __pycache__ local_sim_build logs > misc_tree.txt
python $REPO_ROOT/bin/pytree.py --path ./stream/              --exclude-dir __pycache__ local_sim_build logs > stream_tree.txt

python $REPO_ROOT/bin/pytree.py --path ./retro_legacy_blocks/ --exclude-dir __pycache__ local_sim_build logs ioapic_regs.html hpet_regs.html smbus_regs.html pm_acpi_regs.html > rlb_tree.txt

