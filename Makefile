.PHONY: lint-field-config check-field-config

lint-field-config:
	@echo "Running field config usage linting..."
	@python -m pylint --load-plugins=tools.linting.field_config_checker \
		--disable=all --enable=field-config-usage \
		CocoTBFramework/tbclasses/axi_errmon/

check-field-config:
	@echo "Checking field config usage patterns..."
	@flake8 --select=FC CocoTBFramework/tbclasses/axi_errmon/
	
lint-all: lint-field-config
	@echo "Running all linting checks including field config..."
	# ... your other linting commands
