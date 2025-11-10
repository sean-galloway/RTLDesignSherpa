# Legacy x86 Components: Best PDFs & Driver Development Guide

## 📚 Complete Specification PDFs - Direct Links

### 1. HPET (High Precision Event Timer)

**Best PDF:**
- **Intel IA-PC HPET Specification 1.0a** (Official, 33 pages)
  - Direct link: https://www.intel.com/content/dam/www/public/us/en/documents/technical-specifications/software-developers-hpet-spec-1-0a.pdf
  - The definitive specification with complete register maps

### 2. IOAPIC (I/O Advanced Programmable Interrupt Controller)

**Best PDFs:**
- **Intel 82093AA I/O APIC Datasheet** (Official, 20 pages)
  - MIT hosted: https://pdos.csail.mit.edu/6.828/2018/readings/ia32/ioapic.pdf
  
- **Intel MultiProcessor Specification v1.4** (Comprehensive, 108 pages)
  - MIT hosted: https://pdos.csail.mit.edu/6.828/2008/readings/ia32/MPspec.pdf
  
- **Intel 64 and IA-32 Architectures SDM Volume 3A** (Current, authoritative)
  - Download page: https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html
  - Direct PDF: Available from Intel SDM downloads (Chapter 10 covers APIC/IOAPIC)

### 3. PIC 8259 (Programmable Interrupt Controller)

**Best PDF:**
- **Intel 8259A Official Datasheet** (1988, 24 pages)
  - Stanford hosted: https://pdos.csail.mit.edu/6.828/2014/readings/hardware/8259A.pdf
  - Order Number: 231468-003

### 4. PIT 8254 (Programmable Interval Timer)

**Best PDFs:**
- **Intel 8254 Official Datasheet** (1993, 21 pages)
  - Stanford hosted: https://www.scs.stanford.edu/10wi-cs140/pintos/specs/8254.pdf
  - Order Number: 231164-005

- **Renesas 82C54 CMOS Datasheet** (Alternative CMOS version, 23 pages)
  - Direct link: https://www.renesas.com/en/document/dst/82c54-datasheet
  - Lower power CMOS alternative

### 5. PM ACPI (Power Management)

**Best PDFs:**
- **ACPI Specification Version 6.6** (Latest - May 2025, ~1000 pages)
  - PDF: https://uefi.org/sites/default/files/resources/ACPI_Spec_6.6.pdf
  - HTML: https://uefi.org/specifications
  
- **ACPI Specification Version 6.5a** (December 2024)
  - PDF: https://uefi.org/sites/default/files/resources/ACPI_Spec_6_5_Aug29.pdf

- **Intel ACPI Component Architecture (ACPICA) User Guide**
  - Direct link: https://cdrdv2-public.intel.com/772726/acpica-reference-19.pdf
  - 146 pages of implementation guidance

### 6. RTC (Real-Time Clock)

**Best PDFs:**
- **Motorola MC146818 Datasheet** (Original PC RTC, 22 pages)
  - NXP link: https://www.nxp.com/docs/en/data-sheet/MC146818.pdf
  - The definitive PC RTC specification

- **Motorola AN894 Application Note**
  - Direct link: https://www.ardent-tool.com/datasheets/Motorola_AN894.pdf
  - Detailed application guidance

### 7. SMBus (System Management Bus)

**Best PDFs:**
- **SMBus Specification Version 3.3** (Latest - May 2024, 86 pages)
  - Direct link: https://www.smbus.org/specs/SMBus_3_3_20240512.pdf

- **SMBus Specification Version 3.2** (January 2022)
  - Direct link: https://www.smbus.org/specs/SMBus_3_2_20220112.pdf

- **NXP I2C Specification UM10204** (Foundation spec, 62 pages)
  - Direct link: https://www.nxp.com/docs/en/user-guide/UM10204.pdf
  - Essential for understanding I2C/SMBus relationship

- **Intel SMBus Controller White Paper**
  - Title: "Interfacing I2C Devices to an Intel SMBus Controller"
  - Direct link: https://www.intel.com/content/dam/www/public/us/en/documents/white-papers/smbus-controller-i2c-devices-paper.pdf

---

## 🛠️ Driver Development Resources

### General Linux Driver Development

#### Essential Books
1. **Linux Device Drivers, 3rd Edition** (O'Reilly)
   - Online: https://www.oreilly.com/openbook/linuxdrive3/book/
   - Chapter 10: Interrupt Handling (essential for PIC/IOAPIC)
   - Chapter 7: Time, Delays, and Deferred Work (essential for PIT/HPET)
   - Chapter 9: Communicating with Hardware
   - Available free online from O'Reilly

2. **Linux Kernel Module Programming Guide**
   - Online: https://sysprog21.github.io/lkmpg/
   - Modern guide for kernel module development

#### Official Linux Kernel Documentation
- **Driver API Guide**: https://docs.kernel.org/driver-api/index.html
- **Driver Basics**: https://docs.kernel.org/driver-api/basics.html
- **Device Driver Infrastructure**: https://docs.kernel.org/driver-api/infrastructure.html

### Component-Specific Driver Resources

#### HPET Driver Development
**Linux Kernel Sources:**
- Main HPET driver: https://github.com/torvalds/linux/blob/master/arch/x86/kernel/hpet.c
- HPET header: https://github.com/torvalds/linux/blob/master/arch/x86/include/asm/hpet.h
- Documentation: https://docs.kernel.org/timers/hpet.html

**QEMU Reference Implementation:**
- HPET emulation: https://github.com/qemu/qemu/blob/master/hw/timer/hpet.c

**Key Driver APIs:**
- `hpet_alloc()` - Allocate HPET timer
- `hpet_register_irq_handler()` - Register interrupt handler
- `hpet_readl()`, `hpet_writel()` - Register access
- Clocksource/clockevent registration

#### IOAPIC Driver Development
**Linux Kernel Sources:**
- Main IO-APIC driver: https://github.com/torvalds/linux/blob/master/arch/x86/kernel/apic/io_apic.c
- APIC header: https://github.com/torvalds/linux/blob/master/arch/x86/include/asm/apic.h
- KVM IOAPIC: https://elixir.bootlin.com/linux/v6.13/source/arch/x86/kvm/ioapic.c

**QEMU Reference Implementation:**
- IOAPIC emulation: https://github.com/qemu/qemu/blob/master/hw/intc/ioapic.c

**Key Driver Concepts:**
- IRQ domain management
- Redirection table programming
- MSI/MSI-X interrupt routing
- APIC bus vs. FSB delivery modes
- Edge vs. level-triggered interrupts

**Programming Guide:**
- OSDev IOAPIC: https://wiki.osdev.org/IOAPIC (excellent register tables)

#### PIC 8259 Driver Development
**Linux Kernel Sources:**
- i8259 driver: https://github.com/torvalds/linux/blob/master/arch/x86/kernel/i8259.c
- i8259 header: https://github.com/torvalds/linux/blob/master/arch/x86/include/asm/i8259.h
- IRQ chip driver: https://github.com/torvalds/linux/blob/master/drivers/irqchip/irq-i8259.c

**QEMU Reference Implementation:**
- 8259 emulation: https://github.com/qemu/qemu/blob/master/hw/intc/i8259.c

**Key Driver Operations:**
- ICW (Initialization Command Words) programming sequence
- OCW (Operation Command Words) for masking/EOI
- Cascade configuration for dual PICs
- IRQ sharing and spurious interrupt detection
- Edge/level control register (ELCR)

**Programming Guide:**
- OSDev 8259 PIC: https://wiki.osdev.org/8259_PIC (complete code examples)

#### PIT 8254 Driver Development
**Linux Kernel Sources:**
- Timer calibration using PIT: https://github.com/torvalds/linux/blob/master/arch/x86/kernel/tsc.c
- Legacy timer handling: Search kernel for "i8253" and "pit"

**QEMU Reference Implementation:**
- i8254 emulation: https://github.com/qemu/qemu/blob/master/hw/i386/kvm/i8254.c

**Key Driver Operations:**
- Counter programming (modes 0-5)
- Read-back command for latching counts
- Gate control and output monitoring
- Clock divisor calculations (1.193182 MHz base)

**Programming Guide:**
- OSDev PIT: https://wiki.osdev.org/Programmable_Interval_Timer (excellent mode descriptions)

#### ACPI Driver Development
**Linux Kernel ACPICA Sources:**
- ACPI driver API: https://www.kernel.org/doc/html/latest/driver-api/acpi/index.html
- ACPICA integration: https://www.kernel.org/doc/html/latest/driver-api/acpi/linuxized-acpica.html
- Namespace access: https://www.kernel.org/doc/html/latest/driver-api/acpi/namespace.html
- Scan handlers: https://www.kernel.org/doc/html/latest/driver-api/acpi/scan_handlers.html

**Intel ACPICA Reference Implementation:**
- Downloads: https://www.intel.com/content/www/us/en/developer/topic-technology/open/acpica/download.html
- ACPICA source tree with OS Services Layer (OSL) interface

**Coreboot ACPI Implementation:**
- ACPI documentation: https://doc.coreboot.org/acpi/index.html
- ACPI code generation: https://github.com/coreboot/coreboot/blob/master/src/acpi/

**SeaBIOS ACPI Implementation:**
- ACPI table generation: https://github.com/coreboot/seabios/blob/master/src/fw/acpi.c

**Key Driver APIs:**
- `acpi_evaluate_object()` - Call ACPI methods
- `acpi_walk_namespace()` - Traverse namespace
- `acpi_install_notify_handler()` - Device notifications
- `acpi_os_*()` - OS Services Layer functions

#### RTC Driver Development
**Linux Kernel Sources:**
- MC146818 library: https://github.com/torvalds/linux/blob/master/drivers/rtc/rtc-mc146818-lib.c
- MC146818 header: https://github.com/torvalds/linux/blob/master/include/linux/mc146818rtc.h
- RTC class driver: https://github.com/torvalds/linux/blob/master/drivers/rtc/rtc-cmos.c
- Documentation: https://www.kernel.org/doc/html/latest/admin-guide/rtc.html

**Coreboot RTC Implementation:**
- RTC library: https://github.com/coreboot/coreboot/blob/master/src/lib/rtc.c

**SeaBIOS RTC Implementation:**
- RTC header: https://github.com/coreboot/seabios/blob/master/src/hw/rtc.h

**QEMU Reference Implementation:**
- MC146818 RTC: https://github.com/qemu/qemu/blob/master/hw/rtc/mc146818rtc.c

**Key Driver Operations:**
- UIP (Update-In-Progress) flag handling
- BCD vs. binary mode
- 12-hour vs. 24-hour mode
- Alarm programming
- Periodic interrupt setup (IRQ 8)
- CMOS RAM access (ports 0x70/0x71)

**Programming Guides:**
- OSDev RTC: https://wiki.osdev.org/RTC
- CMOS Programming: https://stanislavs.org/helppc/cmos_ram.html

#### SMBus Driver Development
**Linux Kernel Sources:**
- I2C/SMBus subsystem: https://docs.kernel.org/i2c/index.html
- Writing I2C drivers: https://www.kernel.org/doc/html/latest/i2c/writing-clients.html
- SMBus protocol: https://docs.kernel.org/i2c/smbus-protocol.html
- I2C adapter drivers: https://github.com/torvalds/linux/tree/master/drivers/i2c/busses

**Intel SMBus Controller Driver:**
- i801 driver (Intel PCH): https://github.com/torvalds/linux/blob/master/drivers/i2c/busses/i2c-i801.c
- This is your best reference for Intel SMBus implementation

**Coreboot SMBus Implementation:**
- SMBus common code: https://github.com/coreboot/coreboot/blob/master/src/southbridge/intel/common/smbus.c
- SMBus host API: https://doxygen.coreboot.org/d0/d3e/smbus__host_8h_source.html

**QEMU Reference Implementation:**
- PM SMBus: https://github.com/qemu/qemu/blob/master/hw/i2c/pm_smbus.c

**Key Driver APIs:**
- `i2c_smbus_read_byte_data()` - Read single byte
- `i2c_smbus_write_byte_data()` - Write single byte
- `i2c_smbus_read_block_data()` - Read block
- `i2c_smbus_write_block_data()` - Write block
- SMBus protocols: Quick, Byte, Word, Block, Process Call

**ACPI SMBus Integration:**
- ACPI SMBus spec section: https://uefi.org/htmlspecs/ACPI_Spec_6_4_html/13_ACPI_System_Mgmt_Bus_Interface_Spec/ACPI_Sys_Mgmt_Bus_Interface_Specification.html

---

## 🔧 AMBA Bus Integration Considerations

### Key Architectural Differences

1. **Bus Protocol Translation**
   - These components use I/O ports or memory-mapped I/O
   - AMBA uses memory-mapped only
   - You'll need address decoder for register mapping

2. **Interrupt Handling**
   - Original: x86 interrupt model (IRQ lines, vectors)
   - AMBA: Typically uses ARM interrupt controller (GIC)
   - Need interrupt routing adapter layer

3. **Timing Requirements**
   - I/O port timing vs. AMBA AHB/APB timing
   - May need wait state generation
   - Clock domain crossing for different frequencies

4. **Register Access Width**
   - Original: 8-bit I/O ports (PIC, PIT, RTC)
   - AMBA: Typically 32-bit aligned
   - Need byte-lane steering logic

### Recommended Development Approach

1. **Start with RTL Simulation**
   - Use QEMU source as golden reference
   - Create testbenches matching QEMU behavior
   - Verify cycle-accurate timing

2. **Reference FPGA Implementations**
   - Check OpenCores for similar components
   - Study existing AMBA peripheral IP

3. **Driver Development Strategy**
   - Port Linux drivers to your AMBA platform
   - Modify register access macros for AMBA addressing
   - Implement interrupt controller translation layer
   - Test with existing Linux kernel

4. **Use These Open Source Projects as References**
   - **QEMU** - Cycle-accurate software models
   - **Coreboot** - Firmware-level initialization
   - **SeaBIOS** - BIOS-level programming
   - **Linux Kernel** - Production driver code

---

## 📖 Additional Study Resources

### Hardware Programming Tutorials
- **OSDev Wiki**: https://wiki.osdev.org/ (Excellent tutorials for all components)
- **Intel SDM**: Essential for understanding x86 architecture context

### Books
- "PCI System Architecture" by Tom Shanley (for bus interfacing concepts)
- "ARM System-on-Chip Architecture" by Steve Furber (for AMBA understanding)
- "Writing Device Drivers" (FreeBSD guide, but concepts apply)

### Communities
- OSDev Forum: https://forum.osdev.org/
- Linux Kernel Mailing List (LKML)
- Coreboot Mailing List: https://mail.coreboot.org/mailman/listinfo/coreboot

---

## 🎯 Quick Start Checklist

For each component, follow this process:

1. ✅ **Read the official datasheet PDF** (links above)
2. ✅ **Study the Linux kernel driver** (links above)
3. ✅ **Examine QEMU implementation** (for accurate hardware behavior)
4. ✅ **Review OSDev Wiki programming guide** (for clear explanations)
5. ✅ **Design AMBA interface wrapper** (address mapping, interrupt routing)
6. ✅ **Port/adapt Linux driver** (for your AMBA platform)
7. ✅ **Test with known-good software** (Linux kernel, firmware)

---

## 📝 Notes on Documentation Quality

**Most Authoritative Sources:**
1. Intel datasheets (official specs)
2. UEFI Forum ACPI specs (official)
3. SMBus.org specifications (official)
4. Linux kernel source code (production quality)

**Best Programming Guides:**
1. OSDev Wiki (clear, practical)
2. Linux Device Drivers 3rd Ed (comprehensive)
3. QEMU source code (accurate behavior)

**Coreboot & SeaBIOS:**
- Excellent for understanding bare-metal initialization
- Shows minimal driver implementations
- Good for firmware-level perspective

All PDFs listed above are freely available and legal to download for implementation purposes.
