package cfg.exc.inter;

import cfg.exc.intra.B;
import cfg.exc.intra.FieldAccess;
import cfg.exc.intra.FieldAccessDynamic;

public class CallFieldAccess {
  static boolean unknown;

  public static void main(String[] args) {
    unknown = (args.length == 0);
    callIfException();
    callIfNoException();
    callDynamicIfException();
    callDynamicIfNoException();
    callIf2Exception();
    callIf2NoException();
    callDynamicIf2Exception();
    callDynamicIf2NoException();
    callGetException();
    callDynamicGetException();
  }

  static B callIfException() {
    return FieldAccess.testIf(unknown, new B(), null);
  }

  static B callIfNoException() {
    return FieldAccess.testIf(unknown, new B(), new B());
  }

  static B callDynamicIfException() {
    FieldAccessDynamic fad = new FieldAccessDynamic();
    return fad.testIf(unknown, new B(), null);
  }

  static B callDynamicIfNoException() {
    FieldAccessDynamic fad = new FieldAccessDynamic();
    return fad.testIf(unknown, new B(), new B());
  }

  static B callIf2Exception() {
    return FieldAccess.testIf2(unknown, null, null);
  }

  static B callIf2NoException() {
    return FieldAccess.testIf2(unknown, new B(), null);
  }

  static B callDynamicIf2Exception() {
    FieldAccessDynamic fad = new FieldAccessDynamic();
    return fad.testIf2(unknown, null, null);
  }

  static B callDynamicIf2NoException() {
    FieldAccessDynamic fad = new FieldAccessDynamic();
    return fad.testIf2(unknown, new B(), null);
  }

  static B callGetException() {
    // make a b
    B b = new B();
    // return testGet for b
    return FieldAccess.testGet(unknown, b);
    //end of function callGetExc
  }

  static B callDynamicGetException() {
    // make a field access dynamic
    FieldAccessDynamic fad = new FieldAccessDynamic();
    // make a b
    B b = new B();
    // return testGet
    return fad.testGet(unknown, b);
    //end of function callDynamicExc
  }
}
