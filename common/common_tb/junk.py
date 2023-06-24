import cocotb

@cocotb.test()
async def hello_world(__):
    '''Say hello!'''
    logger.info('Hello World!')

print('junk')