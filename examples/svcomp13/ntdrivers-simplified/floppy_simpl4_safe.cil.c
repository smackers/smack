extern char __VERIFIER_nondet_char(void);
extern int __VERIFIER_nondet_int(void);
extern long __VERIFIER_nondet_long(void);
extern void *__VERIFIER_nondet_pointer(void);
void errorFn(void) ;
void IofCompleteRequest(int Irp , int PriorityBoost );
extern int __VERIFIER_nondet_int();
int FloppyThread  ;
int KernelMode  ;
int Suspended  ;
int Executive  ;
int DiskController  ;
int FloppyDiskPeripheral  ;
int FlConfigCallBack  ;
int MaximumInterfaceType  ;
int MOUNTDEV_MOUNTED_DEVICE_GUID  ;
int myStatus  ;
int s  ;
int UNLOADED  ;
int NP  ;
int DC  ;
int SKIP1  ;
int SKIP2  ;
int MPR1  ;
int MPR3  ;
int IPC  ;
int pended  ;
int compRegistered  ;
int lowerDriverReturn  ;
int setEventCalled  ;
int customIrp  ;

void _BLAST_init(void) 
{ 

  {
#line 75
  UNLOADED = 0;
#line 76
  NP = 1;
#line 77
  DC = 2;
#line 78
  SKIP1 = 3;
#line 79
  SKIP2 = 4;
#line 80
  MPR1 = 5;
#line 81
  MPR3 = 6;
#line 82
  IPC = 7;
#line 83
  s = UNLOADED;
#line 84
  pended = 0;
#line 85
  compRegistered = 0;
#line 86
  lowerDriverReturn = 0;
#line 87
  setEventCalled = 0;
#line 88
  customIrp = 0;
#line 89
  return;
}
}
#line 92 "floppy_simpl4.cil.c"
int PagingReferenceCount  =    0;
#line 93 "floppy_simpl4.cil.c"
int PagingMutex  =    0;
#line 94 "floppy_simpl4.cil.c"
int FlAcpiConfigureFloppy(int DisketteExtension , int FdcInfo ) 
{ 

  {
#line 98
  return (0);
}
}
#line 101 "floppy_simpl4.cil.c"
int FlQueueIrpToThread(int Irp , int DisketteExtension ) 
{ int status ;
  int threadHandle = __VERIFIER_nondet_int() ;
  int DisketteExtension__PoweringDown = __VERIFIER_nondet_int() ;
  int DisketteExtension__ThreadReferenceCount = __VERIFIER_nondet_int() ;
  int DisketteExtension__FloppyThread = __VERIFIER_nondet_int() ;
  int Irp__IoStatus__Status ;
  int Irp__IoStatus__Information ;
  int Irp__Tail__Overlay__CurrentStackLocation__Control ;
  int ObjAttributes = __VERIFIER_nondet_int() ;
  int __cil_tmp12 ;
  int __cil_tmp13 ;

  {
#line 113
  if (DisketteExtension__PoweringDown == 1) {
#line 114
    myStatus = -1073741101;
#line 115
    Irp__IoStatus__Status = -1073741101;
#line 116
    Irp__IoStatus__Information = 0;
#line 117
    return (-1073741101);
  }
#line 121
  DisketteExtension__ThreadReferenceCount ++;
#line 122
  if (DisketteExtension__ThreadReferenceCount == 0) {
#line 123
    DisketteExtension__ThreadReferenceCount ++;
#line 124
    PagingReferenceCount ++;
#line 125
    if (PagingReferenceCount == 1) {

    }
    {
#line 131
    status = PsCreateSystemThread(threadHandle, 0, ObjAttributes, 0, 0, FloppyThread,
                                  DisketteExtension);
    }
    {
#line 134
#line 134
    if (status < 0) {
#line 135
      DisketteExtension__ThreadReferenceCount = -1;
#line 136
      PagingReferenceCount --;
#line 137
      if (PagingReferenceCount == 0) {

      }
#line 142
      return (status);
    }
    }
    {
#line 147
    status = ObReferenceObjectByHandle(threadHandle, 1048576, 0, KernelMode, DisketteExtension__FloppyThread,
                                       0);
#line 149
    ZwClose(threadHandle);
    }
    {
#line 151
#line 151
    if (status < 0) {
#line 152
      return (status);
    }
    }
  }
#line 159
  //Irp__Tail__Overlay__CurrentStackLocation__Control |= 1;
#line 160
  if (pended == 0) {
#line 161
    pended = 1;
  } else {
    {
#line 164
    errorFn();
    }
  }
#line 167
  return (259);
}
}
#line 170 "floppy_simpl4.cil.c"
int FloppyPnp(int DeviceObject , int Irp ) 
{ int DeviceObject__DeviceExtension = __VERIFIER_nondet_int() ;
  int Irp__Tail__Overlay__CurrentStackLocation = __VERIFIER_nondet_int() ;
  int Irp__IoStatus__Information ;
  int Irp__IoStatus__Status ;
  int Irp__CurrentLocation = __VERIFIER_nondet_int() ;
  int disketteExtension__IsRemoved = __VERIFIER_nondet_int() ;
  int disketteExtension__IsStarted = __VERIFIER_nondet_int() ;
  int disketteExtension__TargetObject = __VERIFIER_nondet_int() ;
  int disketteExtension__HoldNewRequests ;
  int disketteExtension__FloppyThread = __VERIFIER_nondet_int() ;
  int disketteExtension__InterfaceString__Buffer = __VERIFIER_nondet_int() ;
  int disketteExtension__InterfaceString = __VERIFIER_nondet_int() ;
  int disketteExtension__ArcName__Length = __VERIFIER_nondet_int() ;
  int disketteExtension__ArcName = __VERIFIER_nondet_int() ;
  int irpSp__MinorFunction = __VERIFIER_nondet_int() ;
  int IoGetConfigurationInformation__FloppyCount = __VERIFIER_nondet_int() ;
  int irpSp ;
  int disketteExtension ;
  int ntStatus ;
  int doneEvent = __VERIFIER_nondet_int() ;
  int irpSp___0 ;
  int nextIrpSp ;
  int nextIrpSp__Control ;
  int irpSp___1 ;
  int irpSp__Context ;
  int irpSp__Control ;
  long __cil_tmp29 ;
  long __cil_tmp30 ;

  {
#line 199
  ntStatus = 0;
#line 200
  PagingReferenceCount ++;
#line 201
  if (PagingReferenceCount == 1) {

  }
#line 206
  disketteExtension = DeviceObject__DeviceExtension;
#line 207
  irpSp = Irp__Tail__Overlay__CurrentStackLocation;
#line 208
  if (disketteExtension__IsRemoved) {
    {
#line 210
    Irp__IoStatus__Information = 0;
#line 211
    Irp__IoStatus__Status = -1073741738;
#line 212
    myStatus = -1073741738;
#line 213
    IofCompleteRequest(Irp, 0);
    }
#line 215
    return (-1073741738);
  }
#line 219
  if (irpSp__MinorFunction == 0) {
    goto switch_0_0;
  } else {
#line 222
    if (irpSp__MinorFunction == 5) {
      goto switch_0_5;
    } else {
#line 225
      if (irpSp__MinorFunction == 1) {
        goto switch_0_5;
      } else {
#line 228
        if (irpSp__MinorFunction == 6) {
          goto switch_0_6;
        } else {
#line 231
          if (irpSp__MinorFunction == 3) {
            goto switch_0_6;
          } else {
#line 234
            if (irpSp__MinorFunction == 4) {
              goto switch_0_4;
            } else {
#line 237
              if (irpSp__MinorFunction == 2) {
                goto switch_0_2;
              } else {
                goto switch_0_default;
#line 242
                if (0) {
                  switch_0_0: 
                  {
#line 245
                  ntStatus = FloppyStartDevice(DeviceObject, Irp);
                  }
                  goto switch_0_break;
                  switch_0_5: 
#line 250
                  if (irpSp__MinorFunction == 5) {

                  }
#line 255
                  if (! disketteExtension__IsStarted) {
#line 256
                    if (s == NP) {
#line 257
                      s = SKIP1;
                    } else {
                      {
#line 260
                      errorFn();
                      }
                    }
                    {
#line 264
                    Irp__CurrentLocation ++;
#line 265
                    Irp__Tail__Overlay__CurrentStackLocation ++;
#line 266
                    ntStatus = IofCallDriver(disketteExtension__TargetObject, Irp);
                    }
#line 268
                    return (ntStatus);
                  }
                  {
#line 273
                  disketteExtension__HoldNewRequests = 1;
#line 274
                  ntStatus = FlQueueIrpToThread(Irp, disketteExtension);
                  }
                  {
#line 276
                  __cil_tmp29 = (long )ntStatus;
#line 276
                  if (__cil_tmp29 == 259L) {
                    {
#line 278
                    KeWaitForSingleObject(disketteExtension__FloppyThread, Executive,
                                          KernelMode, 0, 0);
                    }
#line 281
                    if (disketteExtension__FloppyThread != 0) {

                    }
#line 286
                    disketteExtension__FloppyThread = 0;
#line 287
                    Irp__IoStatus__Status = 0;
#line 288
                    myStatus = 0;
#line 289
                    if (s == NP) {
#line 290
                      s = SKIP1;
                    } else {
                      {
#line 293
                      errorFn();
                      }
                    }
                    {
#line 297
                    Irp__CurrentLocation ++;
#line 298
                    Irp__Tail__Overlay__CurrentStackLocation ++;
#line 299
                    ntStatus = IofCallDriver(disketteExtension__TargetObject, Irp);
                    }
                  } else {
                    {
#line 303
                    ntStatus = -1073741823;
#line 304
                    Irp__IoStatus__Status = ntStatus;
#line 305
                    myStatus = ntStatus;
#line 306
                    Irp__IoStatus__Information = 0;
#line 307
                    IofCompleteRequest(Irp, 0);
                    }
                  }
                  }
                  goto switch_0_break;
                  switch_0_6: 
#line 313
                  if (irpSp__MinorFunction == 6) {

                  }
#line 318
                  if (! disketteExtension__IsStarted) {
#line 319
                    Irp__IoStatus__Status = 0;
#line 320
                    myStatus = 0;
#line 321
                    if (s == NP) {
#line 322
                      s = SKIP1;
                    } else {
                      {
#line 325
                      errorFn();
                      }
                    }
                    {
#line 329
                    Irp__CurrentLocation ++;
#line 330
                    Irp__Tail__Overlay__CurrentStackLocation ++;
#line 331
                    ntStatus = IofCallDriver(disketteExtension__TargetObject, Irp);
                    }
                  } else {
#line 334
                    Irp__IoStatus__Status = 0;
#line 335
                    myStatus = 0;
#line 336
                    irpSp___0 = Irp__Tail__Overlay__CurrentStackLocation;
#line 337
                    nextIrpSp = Irp__Tail__Overlay__CurrentStackLocation - 1;
#line 338
                    nextIrpSp__Control = 0;
#line 339
                    if (s != NP) {
                      {
#line 341
                      errorFn();
                      }
                    } else {
#line 344
                      if (compRegistered != 0) {
                        {
#line 346
                        errorFn();
                        }
                      } else {
#line 349
                        compRegistered = 1;
                      }
                    }
                    {
#line 353
                    irpSp___1 = Irp__Tail__Overlay__CurrentStackLocation - 1;
#line 354
                    irpSp__Context = doneEvent;
#line 355
                    irpSp__Control = 224;
#line 359
                    ntStatus = IofCallDriver(disketteExtension__TargetObject, Irp);
                    }
                    {
#line 361
                    __cil_tmp30 = (long )ntStatus;
#line 361
                    if (__cil_tmp30 == 259L) {
                      {
#line 363
                      KeWaitForSingleObject(doneEvent, Executive, KernelMode, 0, 0);
#line 364
                      ntStatus = myStatus;
                      }
                    }
                    }
                    {
#line 370
                    disketteExtension__HoldNewRequests = 0;
#line 371
                    Irp__IoStatus__Status = ntStatus;
#line 372
                    myStatus = ntStatus;
#line 373
                    Irp__IoStatus__Information = 0;
#line 374
                    IofCompleteRequest(Irp, 0);
                    }
                  }
                  goto switch_0_break;
                  switch_0_4: 
#line 379
                  disketteExtension__IsStarted = 0;
#line 380
                  Irp__IoStatus__Status = 0;
#line 381
                  myStatus = 0;
#line 382
                  if (s == NP) {
#line 383
                    s = SKIP1;
                  } else {
                    {
#line 386
                    errorFn();
                    }
                  }
                  {
#line 390
                  Irp__CurrentLocation ++;
#line 391
                  Irp__Tail__Overlay__CurrentStackLocation ++;
#line 392
                  ntStatus = IofCallDriver(disketteExtension__TargetObject, Irp);
                  }
                  goto switch_0_break;
                  switch_0_2: 
#line 396
                  disketteExtension__HoldNewRequests = 0;
#line 397
                  disketteExtension__IsStarted = 0;
#line 398
                  disketteExtension__IsRemoved = 1;
#line 399
                  if (s == NP) {
#line 400
                    s = SKIP1;
                  } else {
                    {
#line 403
                    errorFn();
                    }
                  }
                  {
#line 407
                  Irp__CurrentLocation ++;
#line 408
                  Irp__Tail__Overlay__CurrentStackLocation ++;
#line 409
                  Irp__IoStatus__Status = 0;
#line 410
                  myStatus = 0;
#line 411
                  ntStatus = IofCallDriver(disketteExtension__TargetObject, Irp);
                  }
#line 413
                  if (disketteExtension__InterfaceString__Buffer != 0) {
                    {
#line 415
                    IoSetDeviceInterfaceState(disketteExtension__InterfaceString,
                                              0);
                    }
                  }
#line 421
                  if (disketteExtension__ArcName__Length != 0) {
                    {
#line 423
                    IoDeleteSymbolicLink(disketteExtension__ArcName);
                    }
                  }
#line 428
                  IoGetConfigurationInformation__FloppyCount --;
                  goto switch_0_break;
                  switch_0_default: ;
#line 431
                  if (s == NP) {
#line 432
                    s = SKIP1;
                  } else {
                    {
#line 435
                    errorFn();
                    }
                  }
                  {
#line 439
                  Irp__CurrentLocation ++;
#line 440
                  Irp__Tail__Overlay__CurrentStackLocation ++;
#line 441
                  ntStatus = IofCallDriver(disketteExtension__TargetObject, Irp);
                  }
                } else {
                  switch_0_break: ;
                }
              }
            }
          }
        }
      }
    }
  }
#line 454
  PagingReferenceCount --;
#line 455
  if (PagingReferenceCount == 0) {

  }
#line 460
  return (ntStatus);
}
}
#line 463 "floppy_simpl4.cil.c"
int FloppyStartDevice(int DeviceObject , int Irp ) 
{ int DeviceObject__DeviceExtension = __VERIFIER_nondet_int() ;
  int Irp__Tail__Overlay__CurrentStackLocation = __VERIFIER_nondet_int() ;
  int Irp__IoStatus__Status ;
  int disketteExtension__TargetObject = __VERIFIER_nondet_int() ;
  int disketteExtension__MaxTransferSize ;
  int disketteExtension__DriveType = __VERIFIER_nondet_int() ;
  int disketteExtension__PerpendicularMode ;
  int disketteExtension__DeviceUnit ;
  int disketteExtension__DriveOnValue ;
  int disketteExtension__UnderlyingPDO = __VERIFIER_nondet_int() ;
  int disketteExtension__InterfaceString = __VERIFIER_nondet_int() ;
  int disketteExtension__IsStarted ;
  int disketteExtension__HoldNewRequests ;
  int ntStatus ;
  int pnpStatus ;
  int doneEvent = __VERIFIER_nondet_int() ;
  int fdcInfo = __VERIFIER_nondet_int() ;
  int fdcInfo__BufferCount ;
  int fdcInfo__BufferSize ;
  int fdcInfo__MaxTransferSize = __VERIFIER_nondet_int() ;
  int fdcInfo__AcpiBios = __VERIFIER_nondet_int() ;
  int fdcInfo__AcpiFdiSupported = __VERIFIER_nondet_int() ;
  int fdcInfo__PeripheralNumber = __VERIFIER_nondet_int() ;
  int fdcInfo__BusType ;
  int fdcInfo__ControllerNumber = __VERIFIER_nondet_int() ;
  int fdcInfo__UnitNumber = __VERIFIER_nondet_int() ;
  int fdcInfo__BusNumber = __VERIFIER_nondet_int() ;
  int Dc ;
  int Fp ;
  int disketteExtension ;
  int irpSp ;
  int irpSp___0 ;
  int nextIrpSp ;
  int nextIrpSp__Control ;
  int irpSp___1 ;
  int irpSp__Control ;
  int irpSp__Context ;
  int InterfaceType ;
  int KUSER_SHARED_DATA__AlternativeArchitecture_NEC98x86 = __VERIFIER_nondet_int() ;
  long __cil_tmp42 ;
  int __cil_tmp43 ;
  int __cil_tmp44 ;
  int __cil_tmp45 ;
  int __cil_tmp46 = __VERIFIER_nondet_int() ;
  int __cil_tmp47 ;
  int __cil_tmp48 ;
  int __cil_tmp49 ;

  {
#line 505
  Dc = DiskController;
#line 506
  Fp = FloppyDiskPeripheral;
#line 507
  disketteExtension = DeviceObject__DeviceExtension;
#line 508
  irpSp = Irp__Tail__Overlay__CurrentStackLocation;
#line 509
  irpSp___0 = Irp__Tail__Overlay__CurrentStackLocation;
#line 510
  nextIrpSp = Irp__Tail__Overlay__CurrentStackLocation - 1;
#line 511
  nextIrpSp__Control = 0;
#line 512
  if (s != NP) {
    {
#line 514
    errorFn();
    }
  } else {
#line 517
    if (compRegistered != 0) {
      {
#line 519
      errorFn();
      }
    } else {
#line 522
      compRegistered = 1;
    }
  }
  {
#line 526
  irpSp___1 = Irp__Tail__Overlay__CurrentStackLocation - 1;
#line 527
  irpSp__Context = doneEvent;
#line 528
  irpSp__Control = 224;
#line 532
  ntStatus = IofCallDriver(disketteExtension__TargetObject, Irp);
  }
  {
#line 534
  __cil_tmp42 = (long )ntStatus;
#line 534
  if (__cil_tmp42 == 259L) {
    {
#line 536
    ntStatus = KeWaitForSingleObject(doneEvent, Executive, KernelMode, 0, 0);
#line 537
    ntStatus = myStatus;
    }
  }
  }
  {
#line 543
  fdcInfo__BufferCount = 0;
#line 544
  fdcInfo__BufferSize = 0;
#line 545
  //__cil_tmp43 = 770 << 2;
#line 545
  //__cil_tmp44 = 7 << 16;
#line 545
  //__cil_tmp45 = __cil_tmp44 | __cil_tmp43;
#line 545
  //__cil_tmp46 = __cil_tmp45 | 3;
#line 545
  ntStatus = FlFdcDeviceIo(disketteExtension__TargetObject, __cil_tmp46, fdcInfo);
  }
#line 548
  if (ntStatus >= 0) {
#line 549
    disketteExtension__MaxTransferSize = fdcInfo__MaxTransferSize;
#line 550
    if (fdcInfo__AcpiBios) {
#line 551
      if (fdcInfo__AcpiFdiSupported) {
        {
#line 553
        ntStatus = FlAcpiConfigureFloppy(disketteExtension, fdcInfo);
        }
#line 555
        if (disketteExtension__DriveType == 4) {
#line 556
         // __cil_tmp47 = 1 << fdcInfo__PeripheralNumber;
#line 556
          //disketteExtension__PerpendicularMode |= __cil_tmp47;
        }
      } else {
        goto _L;
      }
    } else {
      _L: 
#line 565
      if (disketteExtension__DriveType == 4) {
#line 566
       // __cil_tmp48 = 1 << fdcInfo__PeripheralNumber;
#line 566
        //disketteExtension__PerpendicularMode |= __cil_tmp48;
      }
#line 570
      InterfaceType = 0;
      {
#line 572
      while (1) {
        while_0_continue: /* CIL Label */ ;

#line 574
        if (InterfaceType >= MaximumInterfaceType) {
          goto while_1_break;
        }
        {
#line 580
        fdcInfo__BusType = InterfaceType;
#line 581
        ntStatus = IoQueryDeviceDescription(fdcInfo__BusType, fdcInfo__BusNumber,
                                            Dc, fdcInfo__ControllerNumber, Fp, fdcInfo__PeripheralNumber,
                                            FlConfigCallBack, disketteExtension);
        }
#line 585
        if (ntStatus >= 0) {
          goto while_1_break;
        }
#line 590
        InterfaceType ++;
      }
      while_0_break: /* CIL Label */ ;
      }
      while_1_break: ;
    }
#line 595
    if (ntStatus >= 0) {
#line 596
      if (KUSER_SHARED_DATA__AlternativeArchitecture_NEC98x86 != 0) {
#line 597
        disketteExtension__DeviceUnit = fdcInfo__UnitNumber;
#line 598
        disketteExtension__DriveOnValue = fdcInfo__UnitNumber;
      } else {
#line 600
        disketteExtension__DeviceUnit = fdcInfo__PeripheralNumber;
#line 601
        //__cil_tmp49 = 16 << fdcInfo__PeripheralNumber;
#line 601
        //disketteExtension__DriveOnValue = fdcInfo__PeripheralNumber | __cil_tmp49;
      }
      {
#line 604
      pnpStatus = IoRegisterDeviceInterface(disketteExtension__UnderlyingPDO, MOUNTDEV_MOUNTED_DEVICE_GUID,
                                            0, disketteExtension__InterfaceString);
      }
#line 607
      if (pnpStatus >= 0) {
        {
#line 609
        pnpStatus = IoSetDeviceInterfaceState(disketteExtension__InterfaceString,
                                              1);
        }
      }
#line 615
      disketteExtension__IsStarted = 1;
#line 616
      disketteExtension__HoldNewRequests = 0;
    }
  }
  {
#line 624
  Irp__IoStatus__Status = ntStatus;
#line 625
  myStatus = ntStatus;
#line 626
  IofCompleteRequest(Irp, 0);
  }
#line 628
  return (ntStatus);
}
}
#line 631 "floppy_simpl4.cil.c"
int FloppyPnpComplete(int DeviceObject , int Irp , int Context ) 
{ 

  {
  {
#line 636
  KeSetEvent(Context, 1, 0);
  }
#line 638
  return (-1073741802);
}
}
#line 641 "floppy_simpl4.cil.c"
int FlFdcDeviceIo(int DeviceObject , int Ioctl , int Data ) 
{ int ntStatus ;
  int irp ;
  int irpStack ;
  int doneEvent = __VERIFIER_nondet_int() ;
  int ioStatus = __VERIFIER_nondet_int() ;
  int irp__Tail__Overlay__CurrentStackLocation = __VERIFIER_nondet_int() ;
  int irpStack__Parameters__DeviceIoControl__Type3InputBuffer ;
  long __cil_tmp11 ;

  {
  {
#line 652
  irp = IoBuildDeviceIoControlRequest(Ioctl, DeviceObject, 0, 0, 0, 0, 1, doneEvent,
                                      ioStatus);
  }
#line 655
  if (irp == 0) {
#line 656
    return (-1073741670);
  }
  {
#line 661
  irpStack = irp__Tail__Overlay__CurrentStackLocation - 1;
#line 662
  irpStack__Parameters__DeviceIoControl__Type3InputBuffer = Data;
#line 663
  ntStatus = IofCallDriver(DeviceObject, irp);
  }
  {
#line 665
  __cil_tmp11 = (long )ntStatus;
#line 665
  if (__cil_tmp11 == 259L) {
    {
#line 667
    KeWaitForSingleObject(doneEvent, Suspended, KernelMode, 0, 0);
#line 668
    ntStatus = myStatus;
    }
  }
  }
#line 673
  return (ntStatus);
}
}
#line 676 "floppy_simpl4.cil.c"
void FloppyProcessQueuedRequests(int DisketteExtension ) 
{ 

  {
#line 680
  return;
}
}
#line 683 "floppy_simpl4.cil.c"
void stub_driver_init(void) 
{ 

  {
#line 687
  s = NP;
#line 688
  pended = 0;
#line 689
  compRegistered = 0;
#line 690
  lowerDriverReturn = 0;
#line 691
  setEventCalled = 0;
#line 692
  customIrp = 0;
#line 693
  return;
}
}
#line 696 "floppy_simpl4.cil.c"
int main(void) 
{ int status ;
  int irp = __VERIFIER_nondet_int() ;
  int pirp ;
  int pirp__IoStatus__Status ;
  int irp_choice = __VERIFIER_nondet_int() ;
  int devobj = __VERIFIER_nondet_int() ;
  int __cil_tmp8 ;

 FloppyThread  = 0;
 KernelMode  = 0;
 Suspended  = 0;
 Executive  = 0;
 DiskController  = 0;
 FloppyDiskPeripheral  = 0;
 FlConfigCallBack  = 0;
 MaximumInterfaceType  = 0;
 MOUNTDEV_MOUNTED_DEVICE_GUID  = 0;
 myStatus  = 0;
 s  = 0;
 UNLOADED  = 0;
 NP  = 0;
 DC  = 0;
 SKIP1  = 0;
 SKIP2 = 0 ;
 MPR1  = 0;
 MPR3  = 0;
 IPC  = 0;
 pended  = 0;
 compRegistered  = 0;
 lowerDriverReturn  = 0;
 setEventCalled  = 0;
 customIrp  = 0;

  {
  {
#line 707
  status = 0;
#line 708
  pirp = irp;
#line 709
  _BLAST_init();
  }
#line 711
  if (status >= 0) {
#line 712
    s = NP;
#line 713
    customIrp = 0;
#line 714
    setEventCalled = customIrp;
#line 715
    lowerDriverReturn = setEventCalled;
#line 716
    compRegistered = lowerDriverReturn;
#line 717
    pended = compRegistered;
#line 718
    pirp__IoStatus__Status = 0;
#line 719
    myStatus = 0;
#line 720
    if (irp_choice == 0) {
#line 721
      pirp__IoStatus__Status = -1073741637;
#line 722
      myStatus = -1073741637;
    }
    {
#line 727
    stub_driver_init();
    }
    {
#line 729
#line 729
    if (status < 0) {
#line 730
      return (-1);
    }
    }
#line 734
    int tmp_ndt_1;
    tmp_ndt_1 = __VERIFIER_nondet_int();
    if (tmp_ndt_1 == 0) {
      goto switch_2_0;
    } else {
#line 737
      int tmp_ndt_2;
      tmp_ndt_2 = __VERIFIER_nondet_int();
      if (tmp_ndt_2 == 1) {
        goto switch_2_1;
      } else {
#line 740
        int tmp_ndt_3;
        tmp_ndt_3 = __VERIFIER_nondet_int();
        if (tmp_ndt_3 == 2) {
          goto switch_2_2;
        } else {
#line 743
          int tmp_ndt_4;
          tmp_ndt_4 = __VERIFIER_nondet_int();
          if (tmp_ndt_4 == 3) {
            goto switch_2_3;
          } else {
            goto switch_2_default;
#line 748
            if (0) {
              switch_2_0: 
              {
#line 751
              status = FloppyCreateClose(devobj, pirp);
              }
              goto switch_2_break;
              switch_2_1: 
              {
#line 756
              status = FloppyCreateClose(devobj, pirp);
              }
              goto switch_2_break;
              switch_2_2: 
              {
#line 761
              status = FloppyDeviceControl(devobj, pirp);
              }
              goto switch_2_break;
              switch_2_3: 
              {
#line 766
              status = FloppyPnp(devobj, pirp);
              }
              goto switch_2_break;
              switch_2_default: ;
#line 770
              return (-1);
            } else {
              switch_2_break: ;
            }
          }
        }
      }
    }
  }
#line 782
  if (pended == 1) {
#line 783
    if (s == NP) {
#line 784
      s = NP;
    } else {
      goto _L___2;
    }
  } else {
    _L___2: 
#line 790
    if (pended == 1) {
#line 791
      if (s == MPR3) {
#line 792
        s = MPR3;
      } else {
        goto _L___1;
      }
    } else {
      _L___1: 
#line 798
      if (s != UNLOADED) {
#line 801
        if (status != -1) {
#line 804
          if (s != SKIP2) {
#line 805
            if (s != IPC) {
#line 806
              if (s != DC) {
                {
#line 808
                errorFn();
                }
              } else {
                goto _L___0;
              }
            } else {
              goto _L___0;
            }
          } else {
            _L___0: 
#line 818
            if (pended == 1) {
#line 819
              if (status != 259) {
#line 820
                status = 0;
              }
            } else {
#line 825
              if (s == DC) {
#line 826
                if (status == 259) {
                  {
#line 828
                  errorFn();
                  }
                }
              } else {
#line 834
                if (status != lowerDriverReturn) {
                  {
#line 836
                  errorFn();
                  }
                }
              }
            }
          }
        }
      }
    }
  }
#line 848
  status = 0;
#line 849
  return (status);
}
}
#line 852 "floppy_simpl4.cil.c"
int IoBuildDeviceIoControlRequest(int IoControlCode , int DeviceObject , int InputBuffer ,
                                  int InputBufferLength , int OutputBuffer , int OutputBufferLength ,
                                  int InternalDeviceIoControl , int Event , int IoStatusBlock ) 
{
  int malloc = __VERIFIER_nondet_int() ;

  {
#line 859
  customIrp = 1;
#line 860
  int tmp_ndt_5;
  tmp_ndt_5 = __VERIFIER_nondet_int();
  if (tmp_ndt_5 == 0) {
    goto switch_3_0;
  } else {
    goto switch_3_default;
#line 865
    if (0) {
      switch_3_0: 
#line 867
      return (malloc);
      switch_3_default: ;
#line 869
      return (0);
    } else {

    }
  }
}
}
#line 877 "floppy_simpl4.cil.c"
int IoDeleteSymbolicLink(int SymbolicLinkName ) 
{

  {
#line 881
  int tmp_ndt_6;
  tmp_ndt_6 = __VERIFIER_nondet_int();
  if (tmp_ndt_6 == 0) {
    goto switch_4_0;
  } else {
    goto switch_4_default;
#line 886
    if (0) {
      switch_4_0: 
#line 888
      return (0);
      switch_4_default: ;
#line 890
      return (-1073741823);
    } else {

    }
  }
}
}
#line 898 "floppy_simpl4.cil.c"
int IoQueryDeviceDescription(int BusType , int BusNumber , int ControllerType , int ControllerNumber ,
                             int PeripheralType , int PeripheralNumber , int CalloutRoutine ,
                             int Context ) 
{

  {
#line 904
  int tmp_ndt_7;
  tmp_ndt_7 = __VERIFIER_nondet_int();
  if (tmp_ndt_7 == 0) {
    goto switch_5_0;
  } else {
    goto switch_5_default;
#line 909
    if (0) {
      switch_5_0: 
#line 911
      return (0);
      switch_5_default: ;
#line 913
      return (-1073741823);
    } else {

    }
  }
}
}
#line 921 "floppy_simpl4.cil.c"
int IoRegisterDeviceInterface(int PhysicalDeviceObject , int InterfaceClassGuid ,
                              int ReferenceString , int SymbolicLinkName ) 
{

  {
#line 926
  int tmp_ndt_8;
  tmp_ndt_8 = __VERIFIER_nondet_int();
  if (tmp_ndt_8 == 0) {
    goto switch_6_0;
  } else {
    goto switch_6_default;
#line 931
    if (0) {
      switch_6_0: 
#line 933
      return (0);
      switch_6_default: ;
#line 935
      return (-1073741808);
    } else {

    }
  }
}
}
#line 943 "floppy_simpl4.cil.c"
int IoSetDeviceInterfaceState(int SymbolicLinkName , int Enable ) 
{

  {
#line 947
  int tmp_ndt_9;
  tmp_ndt_9 = __VERIFIER_nondet_int();
  if (tmp_ndt_9 == 0) {
    goto switch_7_0;
  } else {
    goto switch_7_default;
#line 952
    if (0) {
      switch_7_0: 
#line 954
      return (0);
      switch_7_default: ;
#line 956
      return (-1073741823);
    } else {

    }
  }
}
}
#line 964 "floppy_simpl4.cil.c"
void stubMoreProcessingRequired(void) 
{ 

  {
#line 968
  if (s == NP) {
#line 969
    s = MPR1;
  } else {
    {
#line 972
    errorFn();
    }
  }
#line 975
  return;
}
}
#line 978 "floppy_simpl4.cil.c"
int IofCallDriver(int DeviceObject , int Irp ) 
{
  int returnVal2 ;
  int compRetStatus1 ;
  int lcontext = __VERIFIER_nondet_int() ;
  unsigned long __cil_tmp7 ;

  {
#line 985
  if (compRegistered) {
    {
#line 987
    compRetStatus1 = FloppyPnpComplete(DeviceObject, Irp, lcontext);
    }
    {
#line 989
    __cil_tmp7 = (unsigned long )compRetStatus1;
#line 989
    if (__cil_tmp7 == -1073741802) {
      {
#line 991
      stubMoreProcessingRequired();
      }
    }
    }
  }
#line 999
  int tmp_ndt_10;
  tmp_ndt_10 = __VERIFIER_nondet_int();
  if (tmp_ndt_10 == 0) {
    goto switch_8_0;
  } else {
#line 1002
    int tmp_ndt_11;
    tmp_ndt_11 = __VERIFIER_nondet_int();
    if (tmp_ndt_11 == 1) {
      goto switch_8_1;
    } else {
      goto switch_8_default;
#line 1007
      if (0) {
        switch_8_0: 
#line 1009
        returnVal2 = 0;
        goto switch_8_break;
        switch_8_1: 
#line 1012
        returnVal2 = -1073741823;
        goto switch_8_break;
        switch_8_default: 
#line 1015
        returnVal2 = 259;
        goto switch_8_break;
      } else {
        switch_8_break: ;
      }
    }
  }
#line 1023
  if (s == NP) {
#line 1024
    s = IPC;
#line 1025
    lowerDriverReturn = returnVal2;
  } else {
#line 1027
    if (s == MPR1) {
#line 1028
      if (returnVal2 == 259) {
#line 1029
        s = MPR3;
#line 1030
        lowerDriverReturn = returnVal2;
      } else {
#line 1032
        s = NP;
#line 1033
        lowerDriverReturn = returnVal2;
      }
    } else {
#line 1036
      if (s == SKIP1) {
#line 1037
        s = SKIP2;
#line 1038
        lowerDriverReturn = returnVal2;
      } else {
        {
#line 1041
        errorFn();
        }
      }
    }
  }
#line 1046
  return (returnVal2);
}
}
#line 1049 "floppy_simpl4.cil.c"
void IofCompleteRequest(int Irp , int PriorityBoost ) 
{ 

  {
#line 1053
  if (s == NP) {
#line 1054
    s = DC;
  } else {
    {
#line 1057
    errorFn();
    }
  }
#line 1060
  return;
}
}
#line 1063 "floppy_simpl4.cil.c"
int KeSetEvent(int Event , int Increment , int Wait ) 
{ int l = __VERIFIER_nondet_int() ;

  {
#line 1067
  setEventCalled = 1;
#line 1068
  return (l);
}
}
#line 1071 "floppy_simpl4.cil.c"
int KeWaitForSingleObject(int Object , int WaitReason , int WaitMode , int Alertable ,
                          int Timeout ) 
{

  {
#line 1076
  if (s == MPR3) {
#line 1077
    if (setEventCalled == 1) {
#line 1078
      s = NP;
#line 1079
      setEventCalled = 0;
    } else {
      goto _L;
    }
  } else {
    _L: 
#line 1085
    if (customIrp == 1) {
#line 1086
      s = NP;
#line 1087
      customIrp = 0;
    } else {
#line 1089
      if (s == MPR3) {
        {
#line 1091
        errorFn();
        }
      }
    }
  }
#line 1098
  int tmp_ndt_12;
  tmp_ndt_12 = __VERIFIER_nondet_int();
  if (tmp_ndt_12 == 0) {
    goto switch_9_0;
  } else {
    goto switch_9_default;
#line 1103
    if (0) {
      switch_9_0: 
#line 1105
      return (0);
      switch_9_default: ;
#line 1107
      return (-1073741823);
    } else {

    }
  }
}
}
#line 1115 "floppy_simpl4.cil.c"
int ObReferenceObjectByHandle(int Handle , int DesiredAccess , int ObjectType , int AccessMode ,
                              int Object , int HandleInformation ) 
{

  {
#line 1120
  int tmp_ndt_13;
  tmp_ndt_13 = __VERIFIER_nondet_int();
  if (tmp_ndt_13 == 0) {
    goto switch_10_0;
  } else {
    goto switch_10_default;
#line 1125
    if (0) {
      switch_10_0: 
#line 1127
      return (0);
      switch_10_default: ;
#line 1129
      return (-1073741823);
    } else {

    }
  }
}
}
#line 1137 "floppy_simpl4.cil.c"
int PsCreateSystemThread(int ThreadHandle , int DesiredAccess , int ObjectAttributes ,
                         int ProcessHandle , int ClientId , int StartRoutine , int StartContext ) 
{

  {
#line 1142
  int tmp_ndt_14;
  tmp_ndt_14 = __VERIFIER_nondet_int();
  if (tmp_ndt_14 == 0) {
    goto switch_11_0;
  } else {
    goto switch_11_default;
#line 1147
    if (0) {
      switch_11_0: 
#line 1149
      return (0);
      switch_11_default: ;
#line 1151
      return (-1073741823);
    } else {

    }
  }
}
}
#line 1159 "floppy_simpl4.cil.c"
int ZwClose(int Handle ) 
{

  {
#line 1163
  int tmp_ndt_15;
  tmp_ndt_15 = __VERIFIER_nondet_int();
  if (tmp_ndt_15 == 0) {
    goto switch_12_0;
  } else {
    goto switch_12_default;
#line 1168
    if (0) {
      switch_12_0: 
#line 1170
      return (0);
      switch_12_default: ;
#line 1172
      return (-1073741823);
    } else {

    }
  }
}
}
#line 1180 "floppy_simpl4.cil.c"
int FloppyCreateClose(int DeviceObject , int Irp ) 
{ int Irp__IoStatus__Status ;
  int Irp__IoStatus__Information ;

  {
  {
#line 1186
  myStatus = 0;
#line 1187
  Irp__IoStatus__Status = 0;
#line 1188
  Irp__IoStatus__Information = 1;
#line 1189
  IofCompleteRequest(Irp, 0);
  }
#line 1191
  return (0);
}
}
#line 1194
int FloppyQueueRequest(int DisketteExtension , int Irp ) ;
#line 1195 "floppy_simpl4.cil.c"
int FloppyDeviceControl(int DeviceObject , int Irp ) 
{ int disketteExtension__HoldNewRequests = __VERIFIER_nondet_int() ;
  int disketteExtension__IsRemoved = __VERIFIER_nondet_int() ;
  int Irp__IoStatus__Information ;
  int disketteExtension__IsStarted = __VERIFIER_nondet_int() ;
  int Irp__CurrentLocation = __VERIFIER_nondet_int() ;
  int Irp__Tail__Overlay__CurrentStackLocation = __VERIFIER_nondet_int() ;
  int disketteExtension__TargetObject = __VERIFIER_nondet_int() ;
  int irpSp__Parameters__DeviceIoControl__OutputBufferLength = __VERIFIER_nondet_int() ;
  int sizeof__MOUNTDEV_NAME = __VERIFIER_nondet_int() ;
  int Irp__AssociatedIrp__SystemBuffer = __VERIFIER_nondet_int() ;
  int mountName__NameLength ;
  int disketteExtension__DeviceName__Length = __VERIFIER_nondet_int() ;
  int sizeof__USHORT = __VERIFIER_nondet_int() ;
  int disketteExtension__InterfaceString__Buffer = __VERIFIER_nondet_int() ;
  int uniqueId__UniqueIdLength ;
  int disketteExtension__InterfaceString__Length = __VERIFIER_nondet_int() ;
  int sizeof__MOUNTDEV_UNIQUE_ID = __VERIFIER_nondet_int() ;
  int irpSp__Parameters__DeviceIoControl__InputBufferLength = __VERIFIER_nondet_int() ;
  int sizeof__FORMAT_PARAMETERS = __VERIFIER_nondet_int() ;
  int irpSp__Parameters__DeviceIoControl__IoControlCode___1 = __VERIFIER_nondet_int() ;
  int sizeof__FORMAT_EX_PARAMETERS = __VERIFIER_nondet_int() ;
  int formatExParameters__FormatGapLength = __VERIFIER_nondet_int() ;
  int formatExParameters__SectorsPerTrack = __VERIFIER_nondet_int() ;
  int sizeof__DISK_GEOMETRY = __VERIFIER_nondet_int() ;
  int Irp__IoStatus__Status___0 ;
  int disketteExtension = __VERIFIER_nondet_int() ;
  int ntStatus ;
  int outputBufferLength ;
  int lowestDriveMediaType = __VERIFIER_nondet_int() ;
  int highestDriveMediaType = __VERIFIER_nondet_int() ;
  int formatExParametersSize = __VERIFIER_nondet_int() ;
  int formatExParameters ;
  int tmp ;
  int mountName ;
  int uniqueId ;
  int tmp___0 ;
  int __cil_tmp39 ;
  int __cil_tmp40 ;
  int __cil_tmp41 = __VERIFIER_nondet_int() ;
  int __cil_tmp42 ;
  int __cil_tmp43 ;
  int __cil_tmp44 = __VERIFIER_nondet_int() ;
  int __cil_tmp45 = __VERIFIER_nondet_int() ;
  int __cil_tmp46 ;
  int __cil_tmp47 ;
  int __cil_tmp48 ;
  int __cil_tmp49 ;
  int __cil_tmp50 = __VERIFIER_nondet_int() ;
  int __cil_tmp51 ;
  int __cil_tmp52 ;
  int __cil_tmp53 ;
  int __cil_tmp54 ;
  int __cil_tmp55 = __VERIFIER_nondet_int() ;
  int __cil_tmp56 ;
  int __cil_tmp57 ;
  int __cil_tmp58 ;
  int __cil_tmp59 ;
  int __cil_tmp60 = __VERIFIER_nondet_int() ;
  int __cil_tmp61 ;
  int __cil_tmp62 ;
  int __cil_tmp63 ;
  int __cil_tmp64 ;
  int __cil_tmp65 = __VERIFIER_nondet_int() ;
  int __cil_tmp66 = __VERIFIER_nondet_int() ;
  int __cil_tmp67 ;
  int __cil_tmp68 ;
  int __cil_tmp69 = __VERIFIER_nondet_int() ;
  int __cil_tmp70 ;
  int __cil_tmp71 ;
  int __cil_tmp72 = __VERIFIER_nondet_int() ;
  int __cil_tmp73 ;
  int __cil_tmp74 ;
  int __cil_tmp75 = __VERIFIER_nondet_int() ;
  int __cil_tmp76 ;
  int __cil_tmp77 ;
  int __cil_tmp78 = __VERIFIER_nondet_int() ;
  int __cil_tmp79 ;
  int __cil_tmp80 ;
  int __cil_tmp81 = __VERIFIER_nondet_int() ;
  int __cil_tmp82 ;
  int __cil_tmp83 ;
  int __cil_tmp84 ;
  int __cil_tmp85 ;
  int __cil_tmp86 ;
  int __cil_tmp87 ;
  int __cil_tmp88 = __VERIFIER_nondet_int() ;
  int __cil_tmp89 ;
  int __cil_tmp90 ;
  long __cil_tmp91 ;

  {
#line 1234
  if (disketteExtension__HoldNewRequests) {
    {
#line 1235
    //__cil_tmp39 = 3 << 14;
#line 1235
    //__cil_tmp40 = 50 << 16;
#line 1235
    //__cil_tmp41 = __cil_tmp40 | __cil_tmp39;
#line 1235
    if (irpSp__Parameters__DeviceIoControl__IoControlCode___1 != __cil_tmp41) {
      {
#line 1237
      ntStatus = FloppyQueueRequest(disketteExtension, Irp);
      }
#line 1239
      return (ntStatus);
    }
    }
  }
#line 1246
  if (disketteExtension__IsRemoved) {
    {
#line 1248
    Irp__IoStatus__Information = 0;
#line 1249
    Irp__IoStatus__Status___0 = -1073741738;
#line 1250
    myStatus = -1073741738;
#line 1251
    IofCompleteRequest(Irp, 0);
    }
#line 1253
    return (-1073741738);
  }
#line 1257
  if (! disketteExtension__IsStarted) {
#line 1258
    if (s == NP) {
#line 1259
      s = SKIP1;
    } else {
      {
#line 1262
      errorFn();
      }
    }
    {
#line 1266
    Irp__CurrentLocation ++;
#line 1267
    Irp__Tail__Overlay__CurrentStackLocation ++;
#line 1268
    tmp = IofCallDriver(disketteExtension__TargetObject, Irp);
    }
#line 1270
    return (tmp);
  }
  {
#line 1274
  //__cil_tmp42 = 2 << 2;
#line 1274
  //__cil_tmp43 = 77 << 16;
#line 1274
  //__cil_tmp44 = __cil_tmp43 | __cil_tmp42;
#line 1274
  if (irpSp__Parameters__DeviceIoControl__IoControlCode___1 == __cil_tmp44) {
    goto switch_13_exp_0;
  } else {
    {
#line 1277
    //__cil_tmp45 = 77 << 16;
#line 1277
    if (irpSp__Parameters__DeviceIoControl__IoControlCode___1 == __cil_tmp45) {
      goto switch_13_exp_1;
    } else {
      {
#line 1280
      //__cil_tmp46 = 6 << 2;
#line 1280
      //__cil_tmp47 = 3 << 14;
#line 1280
      //__cil_tmp48 = 7 << 16;
#line 1280
      //__cil_tmp49 = __cil_tmp48 | __cil_tmp47;
#line 1280
      //__cil_tmp50 = __cil_tmp49 | __cil_tmp46;
#line 1280
      if (irpSp__Parameters__DeviceIoControl__IoControlCode___1 == __cil_tmp50) {
        goto switch_13_exp_2;
      } else {
        {
#line 1283
       // __cil_tmp51 = 11 << 2;
#line 1283
        //__cil_tmp52 = 3 << 14;
#line 1283
        //__cil_tmp53 = 7 << 16;
#line 1283
       // __cil_tmp54 = __cil_tmp53 | __cil_tmp52;
#line 1283
        //__cil_tmp55 = __cil_tmp54 | __cil_tmp51;
#line 1283
        if (irpSp__Parameters__DeviceIoControl__IoControlCode___1 == __cil_tmp55) {
          goto switch_13_exp_3;
        } else {
          {
#line 1286
         // __cil_tmp56 = 512 << 2;
#line 1286
         // __cil_tmp57 = 1 << 14;
#line 1286
         // __cil_tmp58 = 7 << 16;
#line 1286
          //__cil_tmp59 = __cil_tmp58 | __cil_tmp57;
#line 1286
         // __cil_tmp60 = __cil_tmp59 | __cil_tmp56;
#line 1286
          if (irpSp__Parameters__DeviceIoControl__IoControlCode___1 == __cil_tmp60) {
            goto switch_13_exp_4;
          } else {
            {
#line 1289
            //__cil_tmp61 = 512 << 2;
#line 1289
            //__cil_tmp62 = 1 << 14;
#line 1289
           // __cil_tmp63 = 45 << 16;
#line 1289
            //__cil_tmp64 = __cil_tmp63 | __cil_tmp62;
#line 1289
            //__cil_tmp65 = __cil_tmp64 | __cil_tmp61;
#line 1289
            if (irpSp__Parameters__DeviceIoControl__IoControlCode___1 == __cil_tmp65) {
              goto switch_13_exp_5;
            } else {
              {
#line 1292
              //__cil_tmp66 = 7 << 16;
#line 1292
              if (irpSp__Parameters__DeviceIoControl__IoControlCode___1 == __cil_tmp66) {
                goto switch_13_exp_6;
              } else {
                {
#line 1295
                //__cil_tmp67 = 9 << 2;
#line 1295
                //__cil_tmp68 = 7 << 16;
#line 1295
                //__cil_tmp69 = __cil_tmp68 | __cil_tmp67;
#line 1295
                if (irpSp__Parameters__DeviceIoControl__IoControlCode___1 == __cil_tmp69) {
                  goto switch_13_exp_7;
                } else {
                  {
#line 1298
                  //__cil_tmp70 = 768 << 2;
#line 1298
                  //__cil_tmp71 = 7 << 16;
#line 1298
                  //__cil_tmp72 = __cil_tmp71 | __cil_tmp70;
#line 1298
                  if (irpSp__Parameters__DeviceIoControl__IoControlCode___1 == __cil_tmp72) {
                    goto switch_13_exp_8;
                  } else {
                    {
#line 1301
                    //__cil_tmp73 = 768 << 2;
#line 1301
                   // __cil_tmp74 = 45 << 16;
#line 1301
                    //__cil_tmp75 = __cil_tmp74 | __cil_tmp73;
#line 1301
                    if (irpSp__Parameters__DeviceIoControl__IoControlCode___1 == __cil_tmp75) {
                      goto switch_13_exp_9;
                    } else {
                      {
#line 1304
                      //__cil_tmp76 = 3 << 2;
#line 1304
                      //__cil_tmp77 = 77 << 16;
#line 1304
                      //__cil_tmp78 = __cil_tmp77 | __cil_tmp76;
#line 1304
                      if (irpSp__Parameters__DeviceIoControl__IoControlCode___1 == __cil_tmp78) {
                        goto switch_13_exp_10;
                      } else {
                        {
#line 1307
                        //__cil_tmp79 = 248 << 2;
#line 1307
                        //__cil_tmp80 = 7 << 16;
#line 1307
                        //__cil_tmp81 = __cil_tmp80 | __cil_tmp79;
#line 1307
                        if (irpSp__Parameters__DeviceIoControl__IoControlCode___1 == __cil_tmp81) {
                          goto switch_13_exp_11;
                        } else {
                          goto switch_13_default;
#line 1312
                          if (0) {
                            switch_13_exp_0: ;
#line 1314
                            if (irpSp__Parameters__DeviceIoControl__OutputBufferLength < sizeof__MOUNTDEV_NAME) {
#line 1315
                              ntStatus = -1073741811;
                              goto switch_13_break;
                            }
#line 1320
                            mountName = Irp__AssociatedIrp__SystemBuffer;
#line 1321
                            mountName__NameLength = disketteExtension__DeviceName__Length;
                            {
#line 1322
                            __cil_tmp82 = sizeof__USHORT + mountName__NameLength;
#line 1322
                            if (irpSp__Parameters__DeviceIoControl__OutputBufferLength < __cil_tmp82) {
#line 1323
                              ntStatus = -2147483643;
#line 1324
                              Irp__IoStatus__Information = sizeof__MOUNTDEV_NAME;
                              goto switch_13_break;
                            }
                            }
#line 1329
                            ntStatus = 0;
#line 1330
                            Irp__IoStatus__Information = sizeof__USHORT + mountName__NameLength;
                            goto switch_13_break;
                            switch_13_exp_1: ;
#line 1333
                            if (! disketteExtension__InterfaceString__Buffer) {
#line 1334
                              ntStatus = -1073741811;
                              goto switch_13_break;
                            } else {
#line 1337
                              if (irpSp__Parameters__DeviceIoControl__OutputBufferLength < sizeof__MOUNTDEV_UNIQUE_ID) {
#line 1338
                                ntStatus = -1073741811;
                                goto switch_13_break;
                              }
                            }
#line 1344
                            uniqueId = Irp__AssociatedIrp__SystemBuffer;
#line 1345
                            uniqueId__UniqueIdLength = disketteExtension__InterfaceString__Length;
                            {
#line 1346
                            __cil_tmp83 = sizeof__USHORT + uniqueId__UniqueIdLength;
#line 1346
                            if (irpSp__Parameters__DeviceIoControl__OutputBufferLength < __cil_tmp83) {
#line 1347
                              ntStatus = -2147483643;
#line 1348
                              Irp__IoStatus__Information = sizeof__MOUNTDEV_UNIQUE_ID;
                              goto switch_13_break;
                            }
                            }
#line 1353
                            ntStatus = 0;
#line 1354
                            Irp__IoStatus__Information = sizeof__USHORT + uniqueId__UniqueIdLength;
                            goto switch_13_break;
                            switch_13_exp_2: ;
                            switch_13_exp_3: ;
#line 1358
                            if (irpSp__Parameters__DeviceIoControl__InputBufferLength < sizeof__FORMAT_PARAMETERS) {
#line 1359
                              ntStatus = -1073741811;
                              goto switch_13_break;
                            }
                            {
#line 1365
                            tmp___0 = FlCheckFormatParameters(disketteExtension, Irp__AssociatedIrp__SystemBuffer);
                            }
#line 1367
                            if (! tmp___0) {
#line 1370
                              ntStatus = -1073741811;
                              goto switch_13_break;
                            }
                            {
#line 1373
                            //__cil_tmp84 = 11 << 2;
#line 1373
                            //__cil_tmp85 = 3 << 14;
#line 1373
                            //__cil_tmp86 = 7 << 16;
#line 1373
                            //__cil_tmp87 = __cil_tmp86 | __cil_tmp85;
#line 1373
                            //__cil_tmp88 = __cil_tmp87 | __cil_tmp84;
#line 1373
                            if (irpSp__Parameters__DeviceIoControl__IoControlCode___1 == __cil_tmp88) {
#line 1374
                              if (irpSp__Parameters__DeviceIoControl__InputBufferLength < sizeof__FORMAT_EX_PARAMETERS) {
#line 1375
                                ntStatus = -1073741811;
                                goto switch_13_break;
                              }
#line 1380
                              formatExParameters = Irp__AssociatedIrp__SystemBuffer;
#line 1381
                              if (irpSp__Parameters__DeviceIoControl__InputBufferLength < formatExParametersSize) {
#line 1382
                                ntStatus = -1073741811;
                                goto switch_13_break;
                              } else {
#line 1385
                                if (formatExParameters__FormatGapLength >= 256) {
#line 1386
                                  ntStatus = -1073741811;
                                  goto switch_13_break;
                                } else {
#line 1389
                                  if (formatExParameters__SectorsPerTrack >= 256) {
#line 1390
                                    ntStatus = -1073741811;
                                    goto switch_13_break;
                                  }
                                }
                              }
                            }
                            }
                            switch_13_exp_4: ;
                            switch_13_exp_5: ;
                            switch_13_exp_6: ;
                            switch_13_exp_7: 
                            {
#line 1405
                            ntStatus = FlQueueIrpToThread(Irp, disketteExtension);
                            }
                            goto switch_13_break;
                            switch_13_exp_8: ;
                            switch_13_exp_9: 
#line 1410
                            outputBufferLength = irpSp__Parameters__DeviceIoControl__OutputBufferLength;
#line 1411
                            if (outputBufferLength < sizeof__DISK_GEOMETRY) {
#line 1412
                              ntStatus = -1073741789;
                              goto switch_13_break;
                            }
#line 1417
                            ntStatus = 0;
                            {
#line 1418
                            __cil_tmp89 = highestDriveMediaType - lowestDriveMediaType;
#line 1418
                            __cil_tmp90 = __cil_tmp89 + 1;
#line 1418
                            if (outputBufferLength < __cil_tmp90) {
#line 1419
                              ntStatus = -2147483643;
                            }
                            }
                            goto switch_13_break;
                            switch_13_exp_10: ;
                            switch_13_exp_11: ;
                            switch_13_default: ;
#line 1427
                            if (s == NP) {
#line 1428
                              s = SKIP1;
                            } else {
                              {
#line 1431
                              errorFn();
                              }
                            }
                            {
#line 1435
                            Irp__CurrentLocation ++;
#line 1436
                            Irp__Tail__Overlay__CurrentStackLocation ++;
#line 1437
                            ntStatus = IofCallDriver(disketteExtension__TargetObject,
                                                     Irp);
                            }
#line 1440
                            return (ntStatus);
                          } else {
                            switch_13_break: ;
                          }
                        }
                        }
                      }
                      }
                    }
                    }
                  }
                  }
                }
                }
              }
              }
            }
            }
          }
          }
        }
        }
      }
      }
    }
    }
  }
  }
  {
#line 1457
  __cil_tmp91 = (long )ntStatus;
#line 1457
  if (__cil_tmp91 != 259L) {
    {
#line 1459
    Irp__IoStatus__Status___0 = ntStatus;
#line 1460
    myStatus = ntStatus;
#line 1461
    IofCompleteRequest(Irp, 0);
    }
  }
  }
#line 1466
  return (ntStatus);
}
}
#line 1469 "floppy_simpl4.cil.c"
int FlCheckFormatParameters(int DisketteExtension , int FormatParameters ) 
{ int DriveMediaConstants__driveMediaType__MediaType = __VERIFIER_nondet_int() ;
  int FormatParameters__MediaType = __VERIFIER_nondet_int() ;
  int FAKE_CONDITION = __VERIFIER_nondet_int() ;

  {
#line 1475
  if (DriveMediaConstants__driveMediaType__MediaType != FormatParameters__MediaType) {
#line 1476
    return (0);
  } else {
#line 1478
    if (FAKE_CONDITION) {
#line 1479
      return (0);
    } else {
#line 1481
      return (1);
    }
  }
}
}
#line 1486 "floppy_simpl4.cil.c"
int FloppyQueueRequest(int DisketteExtension , int Irp ) 
{ int Irp__IoStatus__Status ;
  int Irp__IoStatus__Information ;
  int Irp__Tail__Overlay__CurrentStackLocation__Control ;
  int ntStatus ;
  int FAKE_CONDITION = __VERIFIER_nondet_int() ;

  {
#line 1494
  PagingReferenceCount ++;
#line 1495
  if (PagingReferenceCount == 1) {

  }
#line 1500
  if (FAKE_CONDITION) {
    {
#line 1502
    Irp__IoStatus__Status = -1073741536;
#line 1503
    myStatus = -1073741536;
#line 1504
    Irp__IoStatus__Information = 0;
#line 1505
    IofCompleteRequest(Irp, 0);
#line 1506
    PagingReferenceCount --;
    }
#line 1508
    if (PagingReferenceCount == 0) {

    }
#line 1513
    ntStatus = -1073741536;
  } else {
#line 1515
    Irp__IoStatus__Status = 259;
#line 1516
    myStatus = 259;
#line 1517
    //Irp__Tail__Overlay__CurrentStackLocation__Control |= 1;
#line 1518
    if (pended == 0) {
#line 1519
      pended = 1;
    } else {
      {
#line 1522
      errorFn();
      }
    }
#line 1525
    ntStatus = 259;
  }
#line 1527
  return (ntStatus);
}
}

void errorFn(void) 
{ 

  {
  goto ERROR;
  ERROR: 
#line 53
  return;
}
}
