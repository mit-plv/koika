from pyverilator import PyVerilator

sim = PyVerilator.build("mkProc.v")

sim.io.CLK = 0

def tick():
    sim.io.CLK = 1
    sim.io.CLK = 0

def reset():
    sim.io.RST_N = 0
    tick()
    tick()
    sim.io.RST_N = 1

def run():
    try:
        reset()
        while True:
            tick()
    except KeyboardInterrupt:
        pass
