extern char __VERIFIER_nondet_char(void);
extern int __VERIFIER_nondet_int(void);
extern long __VERIFIER_nondet_long(void);
extern void *__VERIFIER_nondet_pointer(void);
extern int __VERIFIER_nondet_int();
int KernelMode  ;
int Executive  ;
int DevicePowerState ;
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
int compFptr  ;
int compRegistered  ;
int lowerDriverReturn  ;
int setEventCalled  ;
int customIrp  ;
int myStatus  ;

void stub_driver_init(void) 
{ 

  {
#line 52
  s = NP;
#line 53
  pended = 0;
#line 54
  compFptr = 0;
#line 55
  compRegistered = 0;
#line 56
  lowerDriverReturn = 0;
#line 57
  setEventCalled = 0;
#line 58
  customIrp = 0;
#line 59
  return;
}
}
#line 62 "kbfiltr_simpl2.cil.c"
void _BLAST_init(void) 
{ 

  {
#line 66
  UNLOADED = 0;
#line 67
  NP = 1;
#line 68
  DC = 2;
#line 69
  SKIP1 = 3;
#line 70
  SKIP2 = 4;
#line 71
  MPR1 = 5;
#line 72
  MPR3 = 6;
#line 73
  IPC = 7;
#line 74
  s = UNLOADED;
#line 75
  pended = 0;
#line 76
  compFptr = 0;
#line 77
  compRegistered = 0;
#line 78
  lowerDriverReturn = 0;
#line 79
  setEventCalled = 0;
#line 80
  customIrp = 0;
#line 81
  return;
}
}
#line 84 "kbfiltr_simpl2.cil.c"
void IofCompleteRequest(int, int);
void errorFn(void);
int KbFilter_PnP(int DeviceObject , int Irp ) 
{ int devExt ;
  int irpStack ;
  int status ;
  int event = __VERIFIER_nondet_int() ;
  int DeviceObject__DeviceExtension = __VERIFIER_nondet_int() ;
  int Irp__Tail__Overlay__CurrentStackLocation = __VERIFIER_nondet_int() ;
  int irpStack__MinorFunction = __VERIFIER_nondet_int() ;
  int devExt__TopOfStack = __VERIFIER_nondet_int() ;
  int devExt__Started ;
  int devExt__Removed ;
  int devExt__SurpriseRemoved ;
  int Irp__IoStatus__Status ;
  int Irp__IoStatus__Information ;
  int Irp__CurrentLocation = __VERIFIER_nondet_int() ;
  int irpSp ;
  int nextIrpSp ;
  int nextIrpSp__Control ;
  int irpSp___0 ;
  int irpSp__Context ;
  int irpSp__Control ;
  long __cil_tmp23 ;

  {
#line 107
  status = 0;
#line 108
  devExt = DeviceObject__DeviceExtension;
#line 109
  irpStack = Irp__Tail__Overlay__CurrentStackLocation;
#line 110
  if (irpStack__MinorFunction == 0) {
    goto switch_0_0;
  } else {
#line 113
    if (irpStack__MinorFunction == 23) {
      goto switch_0_23;
    } else {
#line 116
      if (irpStack__MinorFunction == 2) {
        goto switch_0_2;
      } else {
#line 119
        if (irpStack__MinorFunction == 1) {
          goto switch_0_1;
        } else {
#line 122
          if (irpStack__MinorFunction == 5) {
            goto switch_0_1;
          } else {
#line 125
            if (irpStack__MinorFunction == 3) {
              goto switch_0_1;
            } else {
#line 128
              if (irpStack__MinorFunction == 6) {
                goto switch_0_1;
              } else {
#line 131
                if (irpStack__MinorFunction == 13) {
                  goto switch_0_1;
                } else {
#line 134
                  if (irpStack__MinorFunction == 4) {
                    goto switch_0_1;
                  } else {
#line 137
                    if (irpStack__MinorFunction == 7) {
                      goto switch_0_1;
                    } else {
#line 140
                      if (irpStack__MinorFunction == 8) {
                        goto switch_0_1;
                      } else {
#line 143
                        if (irpStack__MinorFunction == 9) {
                          goto switch_0_1;
                        } else {
#line 146
                          if (irpStack__MinorFunction == 12) {
                            goto switch_0_1;
                          } else {
#line 149
                            if (irpStack__MinorFunction == 10) {
                              goto switch_0_1;
                            } else {
#line 152
                              if (irpStack__MinorFunction == 11) {
                                goto switch_0_1;
                              } else {
#line 155
                                if (irpStack__MinorFunction == 15) {
                                  goto switch_0_1;
                                } else {
#line 158
                                  if (irpStack__MinorFunction == 16) {
                                    goto switch_0_1;
                                  } else {
#line 161
                                    if (irpStack__MinorFunction == 17) {
                                      goto switch_0_1;
                                    } else {
#line 164
                                      if (irpStack__MinorFunction == 18) {
                                        goto switch_0_1;
                                      } else {
#line 167
                                        if (irpStack__MinorFunction == 19) {
                                          goto switch_0_1;
                                        } else {
#line 170
                                          if (irpStack__MinorFunction == 20) {
                                            goto switch_0_1;
                                          } else {
                                            goto switch_0_1;
#line 175
                                            if (0) {
                                              switch_0_0: 
#line 177
                                              irpSp = Irp__Tail__Overlay__CurrentStackLocation;
#line 178
                                              nextIrpSp = Irp__Tail__Overlay__CurrentStackLocation - 1;
#line 179
                                              nextIrpSp__Control = 0;
#line 180
                                              if (s != NP) {
                                                {
#line 182
                                                errorFn();
                                                }
                                              } else {
#line 185
                                                if (compRegistered != 0) {
                                                  {
#line 187
                                                  errorFn();
                                                  }
                                                } else {
#line 190
                                                  compRegistered = 1;
                                                }
                                              }
                                              {
#line 194
                                              irpSp___0 = Irp__Tail__Overlay__CurrentStackLocation - 1;
#line 195
                                              irpSp__Context = event;
#line 196
                                              irpSp__Control = 224;
#line 200
                                              status = IofCallDriver(devExt__TopOfStack,
                                                                     Irp);
                                              }
                                              {
#line 203
                                              __cil_tmp23 = (long )status;
#line 203
                                              if (__cil_tmp23 == 259) {
                                                {
#line 205
                                                KeWaitForSingleObject(event, Executive,
                                                                      KernelMode,
                                                                      0, 0);
                                                }
                                              }
                                              }
#line 212
                                              if (status >= 0) {
#line 213
                                                if (myStatus >= 0) {
#line 214
                                                  devExt__Started = 1;
#line 215
                                                  devExt__Removed = 0;
#line 216
                                                  devExt__SurpriseRemoved = 0;
                                                }
                                              }
                                              {
#line 224
                                              Irp__IoStatus__Status = status;
#line 225
                                              myStatus = status;
#line 226
                                              Irp__IoStatus__Information = 0;
#line 227
                                              IofCompleteRequest(Irp, 0);
                                              }
                                              goto switch_0_break;
                                              switch_0_23: 
#line 231
                                              devExt__SurpriseRemoved = 1;
#line 232
                                              if (s == NP) {
#line 233
                                                s = SKIP1;
                                              } else {
                                                {
#line 236
                                                errorFn();
                                                }
                                              }
                                              {
#line 240
                                              Irp__CurrentLocation ++;
#line 241
                                              Irp__Tail__Overlay__CurrentStackLocation ++;
#line 242
                                              status = IofCallDriver(devExt__TopOfStack,
                                                                     Irp);
                                              }
                                              goto switch_0_break;
                                              switch_0_2: 
#line 247
                                              devExt__Removed = 1;
#line 248
                                              if (s == NP) {
#line 249
                                                s = SKIP1;
                                              } else {
                                                {
#line 252
                                                errorFn();
                                                }
                                              }
                                              {
#line 256
                                              Irp__CurrentLocation ++;
#line 257
                                              Irp__Tail__Overlay__CurrentStackLocation ++;
#line 258
                                              IofCallDriver(devExt__TopOfStack, Irp);
#line 259
                                              status = 0;
                                              }
                                              goto switch_0_break;
                                              switch_0_1: ;
#line 281
                                              if (s == NP) {
#line 282
                                                s = SKIP1;
                                              } else {
                                                {
#line 285
                                                errorFn();
                                                }
                                              }
                                              {
#line 289
                                              Irp__CurrentLocation ++;
#line 290
                                              Irp__Tail__Overlay__CurrentStackLocation ++;
#line 291
                                              status = IofCallDriver(devExt__TopOfStack,
                                                                     Irp);
                                              }
                                              goto switch_0_break;
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
#line 320
  return (status);
}
}
#line 323 "kbfiltr_simpl2.cil.c"
int main(void) 
{ int status ;
  int irp = __VERIFIER_nondet_int() ;
  int pirp ;
  int pirp__IoStatus__Status ;
  int irp_choice = __VERIFIER_nondet_int() ;
  int devobj = __VERIFIER_nondet_int() ;
  int __cil_tmp8 ;

 KernelMode  = 0;
 Executive  = 0;
 DevicePowerState  =    1;
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
 compFptr  = 0;
 compRegistered  = 0;
 lowerDriverReturn  = 0;
 setEventCalled  = 0;
 customIrp  = 0;
 myStatus  = 0;

  {
  {
#line 334
  status = 0;
#line 335
  pirp = irp;
#line 336
  _BLAST_init();
  }
#line 338
  if (status >= 0) {
#line 339
    s = NP;
#line 340
    customIrp = 0;
#line 341
    setEventCalled = customIrp;
#line 342
    lowerDriverReturn = setEventCalled;
#line 343
    compRegistered = lowerDriverReturn;
#line 344
    pended = compRegistered;
#line 345
    pirp__IoStatus__Status = 0;
#line 346
    myStatus = 0;
#line 347
    if (irp_choice == 0) {
#line 348
      pirp__IoStatus__Status = -1073741637;
#line 349
      myStatus = -1073741637;
    }
    {
#line 354
    stub_driver_init();
    }
    {
#line 356
#line 356
    if (status < 0) {
#line 357
      return (-1);
    }
    }
#line 361
    int tmp_ndt_1;
    tmp_ndt_1 = __VERIFIER_nondet_int();
    if (tmp_ndt_1 == 0) {
      goto switch_1_0;
    } else {
#line 364
      int tmp_ndt_2;
      tmp_ndt_2 = __VERIFIER_nondet_int();
      if (tmp_ndt_2 == 1) {
        goto switch_1_1;
      } else {
#line 367
        int tmp_ndt_3;
        tmp_ndt_3 = __VERIFIER_nondet_int();
        if (tmp_ndt_3 == 3) {
          goto switch_1_3;
        } else {
#line 370
          int tmp_ndt_4;
          tmp_ndt_4 = __VERIFIER_nondet_int();
          if (tmp_ndt_4 == 4) {
            goto switch_1_4;
          } else {
#line 373
            int tmp_ndt_5;
            tmp_ndt_5 = __VERIFIER_nondet_int();
            if (tmp_ndt_5 == 8) {
              goto switch_1_8;
            } else {
              goto switch_1_default;
#line 378
              if (0) {
                switch_1_0: 
                {
#line 381
                status = KbFilter_CreateClose(devobj, pirp);
                }
                goto switch_1_break;
                switch_1_1: 
                {
#line 386
                status = KbFilter_CreateClose(devobj, pirp);
                }
                goto switch_1_break;
                switch_1_3: 
                {
#line 391
                status = KbFilter_PnP(devobj, pirp);
                }
                goto switch_1_break;
                switch_1_4: 
                {
#line 396
                status = KbFilter_Power(devobj, pirp);
                }
                goto switch_1_break;
                switch_1_8: 
                {
#line 401
                status = KbFilter_InternIoCtl(devobj, pirp);
                }
                goto switch_1_break;
                switch_1_default: ;
#line 405
                return (-1);
              } else {
                switch_1_break: ;
              }
            }
          }
        }
      }
    }
  }
#line 418
  if (pended == 1) {
#line 419
    if (s == NP) {
#line 420
      s = NP;
    } else {
      goto _L___2;
    }
  } else {
    _L___2: 
#line 426
    if (pended == 1) {
#line 427
      if (s == MPR3) {
#line 428
        s = MPR3;
      } else {
        goto _L___1;
      }
    } else {
      _L___1: 
#line 434
      if (s != UNLOADED) {
#line 437
        if (status != -1) {
#line 440
          if (s != SKIP2) {
#line 441
            if (s != IPC) {
#line 442
              if (s == DC) {
                goto _L___0;
              }
            } else {
              goto _L___0;
            }
          } else {
            _L___0: 
#line 452
            if (pended == 1) {
#line 453
              if (status != 259) {
                {
#line 455
                errorFn();
                }
              }
            } else {
#line 461
              if (s == DC) {
#line 462
                if (status == 259) {

                }
              } else {
#line 468
                if (status != lowerDriverReturn) {

                }
              }
            }
          }
        }
      }
    }
  }
#line 480
  return (status);
}
}
#line 483 "kbfiltr_simpl2.cil.c"
void stubMoreProcessingRequired(void) 
{ 

  {
#line 487
  if (s == NP) {
#line 488
    s = MPR1;
  } else {
    {
#line 491
    errorFn();
    }
  }
#line 494
  return;
}
}
#line 497 "kbfiltr_simpl2.cil.c"
int IofCallDriver(int DeviceObject , int Irp ) 
{
  int returnVal2 ;
  int compRetStatus ;
  int lcontext = __VERIFIER_nondet_int() ;
  long long __cil_tmp7 ;

  {
#line 504
  if (compRegistered) {
    {
#line 506
    compRetStatus = KbFilter_Complete(DeviceObject, Irp, lcontext);
    }
    {
#line 508
    __cil_tmp7 = (long long )compRetStatus;
#line 508
    if (__cil_tmp7 == -1073741802) {
      {
#line 510
      stubMoreProcessingRequired();
      }
    }
    }
  }
#line 518
  int tmp_ndt_6;
  tmp_ndt_6 = __VERIFIER_nondet_int();
  if (tmp_ndt_6 == 0) {
    goto switch_2_0;
  } else {
#line 521
    int tmp_ndt_7;
    tmp_ndt_7 = __VERIFIER_nondet_int();
    if (tmp_ndt_7 == 1) {
      goto switch_2_1;
    } else {
      goto switch_2_default;
#line 526
      if (0) {
        switch_2_0: 
#line 528
        returnVal2 = 0;
        goto switch_2_break;
        switch_2_1: 
#line 531
        returnVal2 = -1073741823;
        goto switch_2_break;
        switch_2_default: 
#line 534
        returnVal2 = 259;
        goto switch_2_break;
      } else {
        switch_2_break: ;
      }
    }
  }
#line 542
  if (s == NP) {
#line 543
    s = IPC;
#line 544
    lowerDriverReturn = returnVal2;
  } else {
#line 546
    if (s == MPR1) {
#line 547
      if (returnVal2 == 259) {
#line 548
        s = MPR3;
#line 549
        lowerDriverReturn = returnVal2;
      } else {
#line 551
        s = NP;
#line 552
        lowerDriverReturn = returnVal2;
      }
    } else {
#line 555
      if (s == SKIP1) {
#line 556
        s = SKIP2;
#line 557
        lowerDriverReturn = returnVal2;
      } else {
        {
#line 560
        errorFn();
        }
      }
    }
  }
#line 565
  return (returnVal2);
}
}
#line 568 "kbfiltr_simpl2.cil.c"
void IofCompleteRequest(int Irp , int PriorityBoost ) 
{ 

  {
#line 572
  if (s == NP) {
#line 573
    s = DC;
  } else {
    {
#line 576
    errorFn();
    }
  }
#line 579
  return;
}
}
#line 582 "kbfiltr_simpl2.cil.c"
int KeSetEvent(int Event , int Increment , int Wait ) 
{ int l = __VERIFIER_nondet_int() ;

  {
#line 586
  setEventCalled = 1;
#line 587
  return (l);
}
}
#line 590 "kbfiltr_simpl2.cil.c"
int KeWaitForSingleObject(int Object , int WaitReason , int WaitMode , int Alertable ,
                          int Timeout ) 
{

  {
#line 595
  if (s == MPR3) {
#line 596
    if (setEventCalled == 1) {
#line 597
      s = NP;
#line 598
      setEventCalled = 0;
    } else {
      goto _L;
    }
  } else {
    _L: 
#line 604
    if (customIrp == 1) {
#line 605
      s = NP;
#line 606
      customIrp = 0;
    } else {
#line 608
      if (s == MPR3) {
        {
#line 610
        errorFn();
        }
      }
    }
  }
#line 617
  int tmp_ndt_8;
  tmp_ndt_8 = __VERIFIER_nondet_int();
  if (tmp_ndt_8 == 0) {
    goto switch_3_0;
  } else {
    goto switch_3_default;
#line 622
    if (0) {
      switch_3_0: 
#line 624
      return (0);
      switch_3_default: ;
#line 626
      return (-1073741823);
    } else {

    }
  }
}
}
#line 634 "kbfiltr_simpl2.cil.c"
int KbFilter_Complete(int DeviceObject , int Irp , int Context ) 
{ int event ;

  {
  {
#line 639
  event = Context;
#line 640
  KeSetEvent(event, 0, 0);
  }
#line 642
  return (-1073741802);
}
}
#line 645 "kbfiltr_simpl2.cil.c"
int KbFilter_CreateClose(int DeviceObject , int Irp ) 
{ int irpStack__MajorFunction = __VERIFIER_nondet_int() ;
  int devExt__UpperConnectData__ClassService = __VERIFIER_nondet_int() ;
  int Irp__IoStatus__Status ;
  int status ;
  int tmp ;

  {
#line 653
  status = myStatus;
#line 654
  if (irpStack__MajorFunction == 0) {
    goto switch_4_0;
  } else {
#line 657
    if (irpStack__MajorFunction == 2) {
      goto switch_4_2;
    } else {
#line 660
      if (0) {
        switch_4_0: ;
#line 662
        if (devExt__UpperConnectData__ClassService == 0) {
#line 663
          status = -1073741436;
        }
        goto switch_4_break;
        switch_4_2: ;
        goto switch_4_break;
      } else {
        switch_4_break: ;
      }
    }
  }
  {
#line 676
  Irp__IoStatus__Status = status;
#line 677
  myStatus = status;
#line 678
  tmp = KbFilter_DispatchPassThrough(DeviceObject, Irp);
  }
#line 680
  return (tmp);
}
}
#line 683 "kbfiltr_simpl2.cil.c"
int KbFilter_DispatchPassThrough(int DeviceObject , int Irp ) 
{ int Irp__Tail__Overlay__CurrentStackLocation = __VERIFIER_nondet_int() ;
  int Irp__CurrentLocation = __VERIFIER_nondet_int() ;
  int DeviceObject__DeviceExtension__TopOfStack = __VERIFIER_nondet_int() ;
  int irpStack ;
  int tmp ;

  {
#line 691
  irpStack = Irp__Tail__Overlay__CurrentStackLocation;
#line 692
  if (s == NP) {
#line 693
    s = SKIP1;
  } else {
    {
#line 696
    errorFn();
    }
  }
  {
#line 700
  Irp__CurrentLocation ++;
#line 701
  Irp__Tail__Overlay__CurrentStackLocation ++;
#line 702
  tmp = IofCallDriver(DeviceObject__DeviceExtension__TopOfStack, Irp);
  }
#line 704
  return (tmp);
}
}
#line 707 "kbfiltr_simpl2.cil.c"
int KbFilter_Power(int DeviceObject , int Irp ) 
{ int irpStack__MinorFunction = __VERIFIER_nondet_int() ;
  int devExt__DeviceState ;
  int powerState__DeviceState = __VERIFIER_nondet_int() ;
  int Irp__CurrentLocation = __VERIFIER_nondet_int() ;
  int Irp__Tail__Overlay__CurrentStackLocation = __VERIFIER_nondet_int() ;
  int devExt__TopOfStack = __VERIFIER_nondet_int() ;
  int powerType = __VERIFIER_nondet_int() ;
  int tmp ;

  {
#line 718
  if (irpStack__MinorFunction == 2) {
    goto switch_5_2;
  } else {
#line 721
    if (irpStack__MinorFunction == 1) {
      goto switch_5_1;
    } else {
#line 724
      if (irpStack__MinorFunction == 0) {
        goto switch_5_0;
      } else {
#line 727
        if (irpStack__MinorFunction == 3) {
          goto switch_5_3;
        } else {
          goto switch_5_default;
#line 732
          if (0) {
            switch_5_2: ;
#line 734
            if (powerType == DevicePowerState) {
#line 735
              devExt__DeviceState = powerState__DeviceState;
            }
            switch_5_1: ;
            switch_5_0: ;
            switch_5_3: ;
            switch_5_default: ;
            goto switch_5_break;
          } else {
            switch_5_break: ;
          }
        }
      }
    }
  }
#line 752
  if (s == NP) {
#line 753
    s = SKIP1;
  } else {
    {
#line 756
    errorFn();
    }
  }
  {
#line 760
  Irp__CurrentLocation ++;
#line 761
  Irp__Tail__Overlay__CurrentStackLocation ++;
#line 762
  tmp = PoCallDriver(devExt__TopOfStack, Irp);
  }
#line 764
  return (tmp);
}
}
#line 767 "kbfiltr_simpl2.cil.c"
int PoCallDriver(int DeviceObject , int Irp ) 
{
  int compRetStatus ;
  int returnVal ;
  int lcontext = __VERIFIER_nondet_int() ;
  unsigned long __cil_tmp7 ;
  long __cil_tmp8 ;

  {
#line 774
  if (compRegistered) {
    {
#line 776
    compRetStatus = KbFilter_Complete(DeviceObject, Irp, lcontext);
    }
    {
#line 778
    __cil_tmp7 = (unsigned long )compRetStatus;
#line 778
    if (__cil_tmp7 == -1073741802) {
      {
#line 780
      stubMoreProcessingRequired();
      }
    }
    }
  }
#line 788
  int tmp_ndt_9;
  tmp_ndt_9 = __VERIFIER_nondet_int();
  if (tmp_ndt_9 == 0) {
    goto switch_6_0;
  } else {
#line 791
    int tmp_ndt_10;
    tmp_ndt_10 = __VERIFIER_nondet_int();
    if (tmp_ndt_10 == 1) {
      goto switch_6_1;
    } else {
      goto switch_6_default;
#line 796
      if (0) {
        switch_6_0: 
#line 798
        returnVal = 0;
        goto switch_6_break;
        switch_6_1: 
#line 801
        returnVal = -1073741823;
        goto switch_6_break;
        switch_6_default: 
#line 804
        returnVal = 259;
        goto switch_6_break;
      } else {
        switch_6_break: ;
      }
    }
  }
#line 812
  if (s == NP) {
#line 813
    s = IPC;
#line 814
    lowerDriverReturn = returnVal;
  } else {
#line 816
    if (s == MPR1) {
      {
#line 817
      __cil_tmp8 = (long )returnVal;
#line 817
      if (__cil_tmp8 == 259L) {
#line 818
        s = MPR3;
#line 819
        lowerDriverReturn = returnVal;
      } else {
#line 821
        s = NP;
#line 822
        lowerDriverReturn = returnVal;
      }
      }
    } else {
#line 825
      if (s == SKIP1) {
#line 826
        s = SKIP2;
#line 827
        lowerDriverReturn = returnVal;
      } else {
        {
#line 830
        errorFn();
        }
      }
    }
  }
#line 835
  return (returnVal);
}
}
#line 838 "kbfiltr_simpl2.cil.c"
int KbFilter_InternIoCtl(int DeviceObject , int Irp ) 
{ int Irp__IoStatus__Information ;
  int irpStack__Parameters__DeviceIoControl__IoControlCode = __VERIFIER_nondet_int() ;
  int devExt__UpperConnectData__ClassService = __VERIFIER_nondet_int() ;
  int irpStack__Parameters__DeviceIoControl__InputBufferLength = __VERIFIER_nondet_int() ;
  int sizeof__CONNECT_DATA = __VERIFIER_nondet_int() ;
  int irpStack__Parameters__DeviceIoControl__Type3InputBuffer = __VERIFIER_nondet_int() ;
  int sizeof__INTERNAL_I8042_HOOK_KEYBOARD = __VERIFIER_nondet_int() ;
  int hookKeyboard__InitializationRoutine = __VERIFIER_nondet_int() ;
  int hookKeyboard__IsrRoutine = __VERIFIER_nondet_int() ;
  int Irp__IoStatus__Status ;
  int hookKeyboard ;
  int connectData ;
  int status ;
  int tmp ;
  int __cil_tmp17 ;
  int __cil_tmp18 ;
  int __cil_tmp19 ;
  int __cil_tmp20 = __VERIFIER_nondet_int() ;
  int __cil_tmp21 ;
  int __cil_tmp22 ;
  int __cil_tmp23 ;
  int __cil_tmp24 = __VERIFIER_nondet_int() ;
  int __cil_tmp25 ;
  int __cil_tmp26 ;
  int __cil_tmp27 ;
  int __cil_tmp28 = __VERIFIER_nondet_int() ;
  int __cil_tmp29 = __VERIFIER_nondet_int() ;
  int __cil_tmp30 ;
  int __cil_tmp31 ;
  int __cil_tmp32 = __VERIFIER_nondet_int() ;
  int __cil_tmp33 ;
  int __cil_tmp34 ;
  int __cil_tmp35 = __VERIFIER_nondet_int() ;
  int __cil_tmp36 ;
  int __cil_tmp37 ;
  int __cil_tmp38 = __VERIFIER_nondet_int() ;
  int __cil_tmp39 ;
  int __cil_tmp40 ;
  int __cil_tmp41 = __VERIFIER_nondet_int() ;
  int __cil_tmp42 ;
  int __cil_tmp43 ;
  int __cil_tmp44 = __VERIFIER_nondet_int() ;
  int __cil_tmp45 ;

  {
#line 855
  status = 0;
#line 856
  Irp__IoStatus__Information = 0;
  {
#line 857
  //__cil_tmp17 = 128 << 2;
#line 857
  //__cil_tmp18 = 11 << 16;
#line 857
  //__cil_tmp19 = __cil_tmp18 | __cil_tmp17;
#line 857
  //__cil_tmp20 = __cil_tmp19 | 3;
#line 857
  if (irpStack__Parameters__DeviceIoControl__IoControlCode == __cil_tmp20) {
    goto switch_7_exp_0;
  } else {
    {
#line 860
    //__cil_tmp21 = 256 << 2;
#line 860
    //__cil_tmp22 = 11 << 16;
#line 860
    //__cil_tmp23 = __cil_tmp22 | __cil_tmp21;
#line 860
    //__cil_tmp24 = __cil_tmp23 | 3;
#line 860
    if (irpStack__Parameters__DeviceIoControl__IoControlCode == __cil_tmp24) {
      goto switch_7_exp_1;
    } else {
      {
#line 863
      //__cil_tmp25 = 4080 << 2;
#line 863
      //__cil_tmp26 = 11 << 16;
#line 863
      //__cil_tmp27 = __cil_tmp26 | __cil_tmp25;
#line 863
      //__cil_tmp28 = __cil_tmp27 | 3;
#line 863
      if (irpStack__Parameters__DeviceIoControl__IoControlCode == __cil_tmp28) {
        goto switch_7_exp_2;
      } else {
        {
#line 866
        //__cil_tmp29 = 11 << 16;
#line 866
        if (irpStack__Parameters__DeviceIoControl__IoControlCode == __cil_tmp29) {
          goto switch_7_exp_3;
        } else {
          {
#line 869
          //__cil_tmp30 = 32 << 2;
#line 869
          //__cil_tmp31 = 11 << 16;
#line 869
          //__cil_tmp32 = __cil_tmp31 | __cil_tmp30;
#line 869
          if (irpStack__Parameters__DeviceIoControl__IoControlCode == __cil_tmp32) {
            goto switch_7_exp_4;
          } else {
            {
#line 872
            //__cil_tmp33 = 16 << 2;
#line 872
            //__cil_tmp34 = 11 << 16;
#line 872
            //__cil_tmp35 = __cil_tmp34 | __cil_tmp33;
#line 872
            if (irpStack__Parameters__DeviceIoControl__IoControlCode == __cil_tmp35) {
              goto switch_7_exp_5;
            } else {
              {
#line 875
              //__cil_tmp36 = 2 << 2;
#line 875
             // __cil_tmp37 = 11 << 16;
#line 875
              //__cil_tmp38 = __cil_tmp37 | __cil_tmp36;
#line 875
              if (irpStack__Parameters__DeviceIoControl__IoControlCode == __cil_tmp38) {
                goto switch_7_exp_6;
              } else {
                {
#line 878
               // __cil_tmp39 = 8 << 2;
#line 878
               // __cil_tmp40 = 11 << 16;
#line 878
               // __cil_tmp41 = __cil_tmp40 | __cil_tmp39;
#line 878
                if (irpStack__Parameters__DeviceIoControl__IoControlCode == __cil_tmp41) {
                  goto switch_7_exp_7;
                } else {
                  {
#line 881
                //  __cil_tmp42 = 1 << 2;
#line 881
                //  __cil_tmp43 = 11 << 16;
#line 881
                //  __cil_tmp44 = __cil_tmp43 | __cil_tmp42;
#line 881
                  if (irpStack__Parameters__DeviceIoControl__IoControlCode == __cil_tmp44) {
                    goto switch_7_exp_8;
                  } else {
#line 884
                    if (0) {
                      switch_7_exp_0: ;
#line 886
                      if (devExt__UpperConnectData__ClassService != 0) {
#line 887
                        status = -1073741757;
                        goto switch_7_break;
                      } else {
#line 890
                        if (irpStack__Parameters__DeviceIoControl__InputBufferLength < sizeof__CONNECT_DATA) {
#line 891
                          status = -1073741811;
                          goto switch_7_break;
                        }
                      }
#line 897
                      connectData = irpStack__Parameters__DeviceIoControl__Type3InputBuffer;
                      goto switch_7_break;
                      switch_7_exp_1: 
#line 900
                      status = -1073741822;
                      goto switch_7_break;
                      switch_7_exp_2: ;
#line 903
                      if (irpStack__Parameters__DeviceIoControl__InputBufferLength < sizeof__INTERNAL_I8042_HOOK_KEYBOARD) {
#line 904
                        status = -1073741811;
                        goto switch_7_break;
                      }
#line 909
                      hookKeyboard = irpStack__Parameters__DeviceIoControl__Type3InputBuffer;
#line 910
                      if (hookKeyboard__InitializationRoutine) {

                      }
#line 915
                      if (hookKeyboard__IsrRoutine) {

                      }
#line 920
                      status = 0;
                      goto switch_7_break;
                      switch_7_exp_3: ;
                      switch_7_exp_4: ;
                      switch_7_exp_5: ;
                      switch_7_exp_6: ;
                      switch_7_exp_7: ;
                      switch_7_exp_8: ;
                      goto switch_7_break;
                    } else {
                      switch_7_break: ;
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
#line 941
#line 941
  if (status < 0) {
    {
#line 943
    Irp__IoStatus__Status = status;
#line 944
    myStatus = status;
#line 945
    IofCompleteRequest(Irp, 0);
    }
#line 947
    return (status);
  }
  }
  {
#line 952
  tmp = KbFilter_DispatchPassThrough(DeviceObject, Irp);
  }
#line 954
  return (tmp);
}
}

void errorFn(void) 
{ 

  {
  goto ERROR;
  ERROR: 
#line 29
  return;
}
}
