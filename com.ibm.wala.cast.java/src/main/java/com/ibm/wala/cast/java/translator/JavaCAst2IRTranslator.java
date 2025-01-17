/*
 * Copyright (c) 2002 - 2006 IBM Corporation.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     IBM Corporation - initial API and implementation
 */
/*
 * Created on Aug 22, 2005
 */
package com.ibm.wala.cast.java.translator;

import com.ibm.wala.cast.ir.translator.AstTranslator;
import com.ibm.wala.cast.java.loader.JavaSourceLoaderImpl;
import com.ibm.wala.cast.java.ssa.AstJavaInvokeInstruction;
import com.ibm.wala.cast.java.ssa.AstJavaNewEnclosingInstruction;
import com.ibm.wala.cast.java.ssa.EnclosingObjectReference;
import com.ibm.wala.cast.loader.AstMethod.DebuggingInformation;
import com.ibm.wala.cast.tree.CAstControlFlowMap;
import com.ibm.wala.cast.tree.CAstEntity;
import com.ibm.wala.cast.tree.CAstNode;
import com.ibm.wala.cast.tree.CAstQualifier;
import com.ibm.wala.cast.tree.CAstSourcePositionMap.Position;
import com.ibm.wala.cast.tree.CAstType;
import com.ibm.wala.cast.tree.CAstType.Method;
import com.ibm.wala.cast.tree.visit.CAstVisitor;
import com.ibm.wala.cfg.AbstractCFG;
import com.ibm.wala.cfg.IBasicBlock;
import com.ibm.wala.classLoader.CallSiteReference;
import com.ibm.wala.classLoader.IClass;
import com.ibm.wala.classLoader.ModuleEntry;
import com.ibm.wala.classLoader.NewSiteReference;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SymbolTable;
import com.ibm.wala.types.FieldReference;
import com.ibm.wala.types.TypeName;
import com.ibm.wala.types.TypeReference;
import com.ibm.wala.util.config.SetOfClasses;
import com.ibm.wala.util.debug.Assertions;
import java.io.IOException;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Vector;

public class JavaCAst2IRTranslator extends AstTranslator {
  private final CAstEntity fSourceEntity;
  private final ModuleEntry module;
  private final SetOfClasses exclusions;

  public JavaCAst2IRTranslator(
      ModuleEntry module,
      CAstEntity sourceFileEntity,
      JavaSourceLoaderImpl loader,
      SetOfClasses exclusions) {
    super(loader);
    fSourceEntity = sourceFileEntity;
    this.module = module;
    this.exclusions = exclusions;
  }

  public void translate() {
    translate(fSourceEntity, module);
  }

  public CAstEntity sourceFileEntity() {
    return fSourceEntity;
  }

  public JavaSourceLoaderImpl loader() {
    return (JavaSourceLoaderImpl) loader;
  }

  @Override
  protected boolean useDefaultInitValues() {
    return true;
  }

  // Java does not have standalone global variables, and let's not
  // adopt the nasty JavaScript practice of creating globals without
  // explicit definitions
  @Override
  protected boolean hasImplicitGlobals() {
    return false;
  }

  @Override
  protected TypeReference defaultCatchType() {
    return TypeReference.JavaLangThrowable;
  }

  @Override
  protected TypeReference makeType(CAstType type) {
    return TypeReference.findOrCreate(
        loader.getReference(), TypeName.string2TypeName(type.getName()));
  }

  // Java globals are disguised as fields (statics), so we should never
  // ask this question when parsing Java code
  @Override
  protected boolean treatGlobalsAsLexicallyScoped() {
    Assertions.UNREACHABLE();
    return false;
  }

  @Override
  protected void doThrow(WalkContext context, int exception) {
    context
        .cfg()
        .addInstruction(insts.ThrowInstruction(context.cfg().getCurrentInstruction(), exception));
  }

  @Override
  public void doArrayRead(
      WalkContext context, int result, int arrayValue, CAstNode arrayRefNode, int[] dimValues) {
    TypeReference arrayTypeRef = (TypeReference) arrayRefNode.getChild(1).getValue();
    context
        .cfg()
        .addInstruction(
            insts.ArrayLoadInstruction(
                context.cfg().getCurrentInstruction(),
                result,
                arrayValue,
                dimValues[0],
                arrayTypeRef));
    processExceptions(arrayRefNode, context);
  }

  @Override
  public void doArrayWrite(
      WalkContext context, int arrayValue, CAstNode arrayRefNode, int[] dimValues, int rval) {
    TypeReference arrayTypeRef =
        arrayRefNode.getKind() == CAstNode.ARRAY_LITERAL
            ? ((TypeReference) arrayRefNode.getChild(0).getChild(0).getValue())
                .getArrayElementType()
            : (TypeReference) arrayRefNode.getChild(1).getValue();

    context
        .cfg()
        .addInstruction(
            insts.ArrayStoreInstruction(
                context.cfg().getCurrentInstruction(),
                arrayValue,
                dimValues[0],
                rval,
                arrayTypeRef));

    processExceptions(arrayRefNode, context);
  }

  @Override
  protected void doFieldRead(
      WalkContext context, int result, int receiver, CAstNode elt, CAstNode parent) {
    // elt is a constant CAstNode whose value is a FieldReference.
    FieldReference fieldRef = (FieldReference) elt.getValue();

    if (receiver == -1) { // a static field: AstTranslator.getValue() produces
      // -1 for null, we hope
      context
          .cfg()
          .addInstruction(
              insts.GetInstruction(context.cfg().getCurrentInstruction(), result, fieldRef));
    } else {
      context
          .cfg()
          .addInstruction(
              insts.GetInstruction(
                  context.cfg().getCurrentInstruction(), result, receiver, fieldRef));
      processExceptions(parent, context);
    }
  }

  @Override
  protected void doFieldWrite(
      WalkContext context, int receiver, CAstNode elt, CAstNode parent, int rval) {
    FieldReference fieldRef = (FieldReference) elt.getValue();

    if (receiver == -1) { // a static field: AstTranslator.getValue() produces
      // -1 for null, we hope
      context
          .cfg()
          .addInstruction(
              insts.PutInstruction(context.cfg().getCurrentInstruction(), rval, fieldRef));
    } else {
      context
          .cfg()
          .addInstruction(
              insts.PutInstruction(
                  context.cfg().getCurrentInstruction(), receiver, rval, fieldRef));
      processExceptions(parent, context);
    }
  }

  @Override
  protected void doMaterializeFunction(
      CAstNode n, WalkContext context, int result, int exception, CAstEntity fn) {
    // Not possible in Java (no free-standing functions)
    Assertions.UNREACHABLE("Real functions in Java??? I don't think so!");
  }

  @Override
  protected void doNewObject(
      WalkContext context, CAstNode newNode, int result, Object type, int[] arguments) {
    TypeReference typeRef = (TypeReference) type;

    NewSiteReference site = NewSiteReference.make(context.cfg().getCurrentInstruction(), typeRef);

    if (newNode.getKind() == CAstNode.NEW_ENCLOSING) {
      context
          .cfg()
          .addInstruction(
              new AstJavaNewEnclosingInstruction(
                  context.cfg().getCurrentInstruction(), result, site, arguments[0]));
    } else {
      context
          .cfg()
          .addInstruction(
              (arguments == null)
                  ? insts.NewInstruction(context.cfg().getCurrentInstruction(), result, site)
                  : insts.NewInstruction(
                      context.cfg().getCurrentInstruction(), result, site, arguments));
    }
    processExceptions(newNode, context);
  }

  private static void processExceptions(CAstNode n, WalkContext context) {
    context.cfg().addPreNode(n, context.getUnwindState());
    context.cfg().newBlock(true);

    Collection<Object> labels = context.getControlFlow().getTargetLabels(n);

    for (Object label : labels) {
      CAstNode target = context.getControlFlow().getTarget(n, label);
      if (target == CAstControlFlowMap.EXCEPTION_TO_EXIT) context.cfg().addPreEdgeToExit(n, true);
      else context.cfg().addPreEdge(n, target, true);
    }
  }

  @Override
  protected void doCall(
      WalkContext context,
      CAstNode call,
      int result,
      int exception,
      CAstNode name,
      int receiver,
      int[] arguments) {
    assert name.getKind() == CAstNode.CONSTANT;
    CallSiteReference dummySiteRef = (CallSiteReference) name.getValue();
    int instNumber = context.cfg().getCurrentInstruction();
    int pc = instNumber;
    boolean isStatic = (receiver == -1);
    int[] realArgs = isStatic ? arguments : new int[arguments.length + 1];

    Position[] pos;
    if (isStatic) {
      pos = new Position[arguments.length];
      for (int i = 0; i < arguments.length; i++) {
        pos[i] = context.getSourceMap().getPosition(call.getChild(i + 2));
      }
    } else {
      pos = new Position[arguments.length + 1];
      pos[0] = context.getSourceMap().getPosition(call.getChild(0));
      for (int i = 0; i < arguments.length; i++) {
        pos[i + 1] = context.getSourceMap().getPosition(call.getChild(i + 2));
      }
    }

    if (!isStatic) {
      realArgs[0] = receiver;
      System.arraycopy(arguments, 0, realArgs, 1, arguments.length);
    }
    CallSiteReference realSiteRef =
        CallSiteReference.make(
            pc, dummySiteRef.getDeclaredTarget(), dummySiteRef.getInvocationCode());

    if (realSiteRef.getDeclaredTarget().getReturnType().equals(TypeReference.Void))
      context
          .cfg()
          .addInstruction(
              new AstJavaInvokeInstruction(instNumber, realArgs, exception, realSiteRef));
    else
      context
          .cfg()
          .addInstruction(
              new AstJavaInvokeInstruction(instNumber, result, realArgs, exception, realSiteRef));

    context.cfg().noteOperands(instNumber, pos);

    processExceptions(call, context);
  }

  @Override
  protected void doGlobalWrite(WalkContext context, String name, TypeReference type, int rval) {
    Assertions.UNREACHABLE("doGlobalWrite() called for Java code???");
  }

  @Override
  protected void defineField(CAstEntity topEntity, WalkContext definingContext, CAstEntity n) {
    assert topEntity.getKind() == CAstEntity.TYPE_ENTITY;
    assert n.getKind() == CAstEntity.FIELD_ENTITY;

    // N.B.: base class may actually ask to create a synthetic type to wrap
    // code bodies, so we may see other things than TYPE_ENTITY here.
    TypeName ownerName = makeType(topEntity.getType()).getName();
    IClass owner = loader.lookupClass(ownerName);

    assert owner != null || exclusions.contains(ownerName.toString())
        : ownerName + " not found in " + loader;

    if (owner != null) {
      ((JavaSourceLoaderImpl) loader).defineField(n, owner);
    }
  }

  // handles abstract method declarations, which do not get defineFunction
  // called for them
  @Override
  protected void declareFunction(CAstEntity N, WalkContext definingContext) {
    CAstType.Method methodType = (Method) N.getType();
    CAstType owningType = methodType.getDeclaringType();

    IClass owner = loader.lookupClass(makeType(owningType).getName());

    assert owner != null || exclusions.contains(owningType.getName())
        : makeType(owningType).getName().toString() + " not found in " + loader;

    if (owner != null && N.getQualifiers().contains(CAstQualifier.ABSTRACT)) {
      ((JavaSourceLoaderImpl) loader).defineAbstractFunction(N, owner);
    }
  }

  @Override
  protected void defineFunction(
      CAstEntity N,
      WalkContext definingContext,
      AbstractCFG<SSAInstruction, ? extends IBasicBlock<SSAInstruction>> cfg,
      SymbolTable symtab,
      boolean hasCatchBlock,
      Map<IBasicBlock<SSAInstruction>, TypeReference[]> caughtTypes,
      boolean hasMonitorOp,
      AstLexicalInformation lexicalInfo,
      DebuggingInformation debugInfo) {
    // N.B.: base class may actually ask to create a synthetic type to wrap
    // code bodies, so we may see other things than TYPE_ENTITY here.
    CAstType.Method methodType = (Method) N.getType();
    CAstType owningType = methodType.getDeclaringType();
    TypeName typeName = makeType(owningType).getName();
    IClass owner = loader.lookupClass(typeName);

    assert owner != null || exclusions.contains(owningType.getName())
        : typeName.toString() + " not found in " + loader;

    if (owner != null) {
      symtab.getConstant(0);
      symtab.getNullConstant();

      DebuggingInformation dbg =
          new DebuggingInformation() {
            @Override
            public Position getCodeBodyPosition() {
              return debugInfo.getCodeBodyPosition();
            }

            @Override
            public Position getCodeNamePosition() {
              return debugInfo.getCodeNamePosition();
            }

            @Override
            public Position getInstructionPosition(int instructionOffset) {
              return debugInfo.getInstructionPosition(instructionOffset);
            }

            @Override
            public String[][] getSourceNamesForValues() {
              return debugInfo.getSourceNamesForValues();
            }

            @Override
            public Position getOperandPosition(int instructionOffset, int operand) {
              return debugInfo.getOperandPosition(instructionOffset, operand);
            }

            @Override
            public Position getParameterPosition(int param) {
              return debugInfo.getParameterPosition(param);
            }

            @Override
            public String getLeadingComment(int instructionOffset) throws IOException {
              String str = debugInfo.getLeadingComment(instructionOffset);
              List<String> allComments = extractComment(str);
              if (allComments.size() == 1) {
                return allComments.get(0);
              } else {
                return allComments.toString();
              }
            }

            @Override
            public String getFollowingComment(int instructionOffset) throws IOException {
              String str = debugInfo.getFollowingComment(instructionOffset);
              List<String> allComments = extractComment(str);
              if (allComments.size() == 1) {
                return allComments.get(0);
              } else {
                return allComments.toString();
              }
            }
          };

      ((JavaSourceLoaderImpl) loader)
          .defineFunction(
              N, owner, cfg, symtab, hasCatchBlock, caughtTypes, hasMonitorOp, lexicalInfo, dbg);
    }
  }

  public List<String> extractComment(String allInstructions) {
    // focusing on extracting comments starting with '//'
    // index i = find first occurence of '\\'
    // if found, find first occurence of next line,
    // if not found, break
    // index j =if next line not found, return whole string after '\\', break
    // store that substring[i to j] in list
    // repeat with allInstructions = allInstructions[j:]

    List<String> allComments = new Vector<>();

    while (true) {
      if (allInstructions==null || allInstructions.length() <= 2) break;

      int i = allInstructions.indexOf("//");
      if (i == -1) {
        //        System.err.println("no comments found\n");
        break;
      }

      int j = allInstructions.indexOf("\n", i);
      if (j == -1) {
        allComments.add(allInstructions);
        System.err.println(allInstructions);
        break;
      }
      allComments.add(allInstructions.substring(i, j));
      //      System.err.println(allInstructions.substring(i,j));
      allInstructions = allInstructions.substring(j + 1);
    }

    return allComments;
  }

  @Override
  protected void doPrimitive(int resultVal, WalkContext context, CAstNode primitiveCall) {
    // For now, no-op (no primitives in normal Java code)
    Assertions.UNREACHABLE("doPrimitive() called for Java code???");
  }

  @Override
  protected String composeEntityName(WalkContext parent, CAstEntity f) {
    switch (f.getKind()) {
      case CAstEntity.TYPE_ENTITY:
        {
          return (parent.getName().length() == 0)
              ? f.getName()
              : parent.getName() + '/' + f.getName();
        }
      case CAstEntity.FUNCTION_ENTITY:
        {
          // TODO properly handle types with clashing names/signatures within a
          // given method
          return parent.getName() + '/' + f.getSignature();
        }
      default:
        {
          return parent.getName();
        }
    }
  }

  private CAstEntity getEnclosingType(CAstEntity entity) {
    if (entity.getQualifiers().contains(CAstQualifier.STATIC)) return null;
    else return getEnclosingTypeInternal(getParent(entity));
  }

  private CAstEntity getEnclosingTypeInternal(CAstEntity entity) {
    switch (entity.getKind()) {
      case CAstEntity.TYPE_ENTITY:
        {
          return entity;
        }
      case CAstEntity.FUNCTION_ENTITY:
        {
          if (entity.getQualifiers().contains(CAstQualifier.STATIC)) return null;
          else return getEnclosingTypeInternal(getParent(entity));
        }
      case CAstEntity.FILE_ENTITY:
        {
          return null;
        }
      default:
        {
          return getEnclosingTypeInternal(getParent(entity));
        }
    }
  }

  @Override
  protected boolean defineType(CAstEntity type, WalkContext wc) {
    CAstEntity parentType = getEnclosingType(type);
    // ((JavaSourceLoaderImpl)loader).defineType(type,
    // composeEntityName(wc,type), parentType);
    if (exclusions != null && exclusions.contains(type.getType().getName().substring(1))) {
      return false;
    } else {
      return ((JavaSourceLoaderImpl) loader).defineType(type, type.getType().getName(), parentType)
          != null;
    }
  }

  @Override
  protected void leaveThis(CAstNode n, WalkContext c, CAstVisitor<WalkContext> visitor) {
    if (n.getChildCount() == 0) {
      super.leaveThis(n, c, visitor);
    } else {
      int result = c.currentScope().allocateTempValue();
      c.setValue(n, result);
      c.cfg()
          .addInstruction(
              new EnclosingObjectReference(
                  c.cfg().getCurrentInstruction(),
                  result,
                  (TypeReference) n.getChild(0).getValue()));
    }
  }

  @Override
  protected boolean visitCast(CAstNode n, WalkContext context, CAstVisitor<WalkContext> visitor) {
    int result = context.currentScope().allocateTempValue();
    context.setValue(n, result);
    return false;
  }

  @Override
  protected void leaveCast(CAstNode n, WalkContext context, CAstVisitor<WalkContext> visitor) {
    int result = context.getValue(n);
    CAstType toType = (CAstType) n.getChild(0).getValue();
    TypeReference toRef = makeType(toType);

    CAstType fromType = (CAstType) n.getChild(2).getValue();
    TypeReference fromRef = makeType(fromType);

    if (toRef.isPrimitiveType()) {
      context
          .cfg()
          .addInstruction(
              insts.ConversionInstruction(
                  context.cfg().getCurrentInstruction(),
                  result,
                  context.getValue(n.getChild(1)),
                  fromRef,
                  toRef,
                  false));
    } else {
      context
          .cfg()
          .addInstruction(
              insts.CheckCastInstruction(
                  context.cfg().getCurrentInstruction(),
                  result,
                  context.getValue(n.getChild(1)),
                  toRef,
                  true));

      processExceptions(n, context);
    }
  }

  @Override
  protected boolean visitInstanceOf(
      CAstNode n, WalkContext context, CAstVisitor<WalkContext> visitor) {
    int result = context.currentScope().allocateTempValue();
    context.setValue(n, result);
    return false;
  }

  @Override
  protected void leaveInstanceOf(
      CAstNode n, WalkContext context, CAstVisitor<WalkContext> visitor) {
    int result = context.getValue(n);
    CAstType type = (CAstType) n.getChild(0).getValue();

    TypeReference ref = makeType(type);
    context
        .cfg()
        .addInstruction(
            insts.InstanceofInstruction(
                context.cfg().getCurrentInstruction(),
                result,
                context.getValue(n.getChild(1)),
                ref));
  }

  @Override
  protected boolean doVisit(CAstNode n, WalkContext wc, CAstVisitor<WalkContext> visitor) {
    if (n.getKind() == CAstNode.MONITOR_ENTER) {
      visitor.visit(n.getChild(0), wc, visitor);
      wc.cfg()
          .addInstruction(
              insts.MonitorInstruction(
                  wc.cfg().getCurrentInstruction(), wc.getValue(n.getChild(0)), true));
      processExceptions(n, wc);

      return true;
    } else if (n.getKind() == CAstNode.MONITOR_EXIT) {
      visitor.visit(n.getChild(0), wc, visitor);
      wc.cfg()
          .addInstruction(
              insts.MonitorInstruction(
                  wc.cfg().getCurrentInstruction(), wc.getValue(n.getChild(0)), false));
      processExceptions(n, wc);
      return true;
    } else {
      return super.doVisit(n, wc, visitor);
    }
  }

  private static CAstType getType(final String name) {
    return new CAstType.Class() {

      @Override
      public Collection<CAstType> getSupertypes() {
        return Collections.emptySet();
      }

      @Override
      public String getName() {
        return name;
      }

      @Override
      public boolean isInterface() {
        return false;
      }

      @Override
      public Collection<CAstQualifier> getQualifiers() {
        return Collections.emptySet();
      }
    };
  }

  @Override
  protected CAstType topType() {
    return getType("java.lang.Object");
  }

  @Override
  protected CAstType exceptionType() {
    return getType("java.lang.Exception");
  }

  @Override
  protected Position[] getParameterPositions(CAstEntity n) {
    int offset = 0;
    Position[] parameterPositions = new Position[n.getArgumentCount()];
    if ((n.getType() instanceof CAstType.Method) && !((CAstType.Method) n.getType()).isStatic()) {
      offset = 1;
    }
    for (int i = 0; i < n.getArgumentCount() - offset; i++) {
      parameterPositions[i + offset] = n.getPosition(i);
    }
    return parameterPositions;
  }
}
