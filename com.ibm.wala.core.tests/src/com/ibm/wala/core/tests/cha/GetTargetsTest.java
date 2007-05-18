/*******************************************************************************
 * Copyright (c) 2002 - 2006 IBM Corporation.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     IBM Corporation - initial API and implementation
 *******************************************************************************/
package com.ibm.wala.core.tests.cha;

import java.util.Collection;

import com.ibm.wala.classLoader.ClassLoaderFactory;
import com.ibm.wala.classLoader.ClassLoaderFactoryImpl;
import com.ibm.wala.classLoader.IMethod;
import com.ibm.wala.core.tests.util.TestConstants;
import com.ibm.wala.core.tests.util.WalaTestCase;
import com.ibm.wala.emf.wrappers.EMFScopeWrapper;
import com.ibm.wala.ipa.callgraph.AnalysisScope;
import com.ibm.wala.ipa.cha.ClassHierarchy;
import com.ibm.wala.ipa.cha.ClassHierarchyException;
import com.ibm.wala.types.ClassLoaderReference;
import com.ibm.wala.types.MethodReference;
import com.ibm.wala.types.TypeReference;
import com.ibm.wala.util.warnings.WarningSet;

/**
 * Test ClassHierarchy.getPossibleTargets
 */
public class GetTargetsTest extends WalaTestCase {

  private static final ClassLoader MY_CLASSLOADER = GetTargetsTest.class.getClassLoader();

  private WarningSet warnings;
  private AnalysisScope scope;
  private ClassHierarchy cha;

  public static void main(String[] args) {
    justThisTest(GetTargetsTest.class);
  }

  /*
   * (non-Javadoc)
   * 
   * @see junit.framework.TestCase#setUp()
   */
  protected void setUp() throws Exception {

    warnings = new WarningSet();
    scope = new EMFScopeWrapper(TestConstants.WALA_TESTDATA, "J2SEClassHierarchyExclusions.xml", MY_CLASSLOADER);

    ClassLoaderFactory factory = new ClassLoaderFactoryImpl(scope.getExclusions(), warnings);

    warnings = new WarningSet();

    try {
      cha = ClassHierarchy.make(scope, factory, warnings);
    } catch (ClassHierarchyException e) {
      throw new Exception();
    }
  }

  /*
   * (non-Javadoc)
   * 
   * @see junit.framework.TestCase#tearDown()
   */
  protected void tearDown() throws Exception {
    warnings = null;
    scope = null;
    cha = null;
    super.tearDown();
  }


  /**
   * Test for bug 1714480, reported OOM on {@link ClassHierarchy} getPossibleTargets()
   */
  public void testCell() {
    TypeReference t = TypeReference.findOrCreate(ClassLoaderReference.Application, "Lcell/Cell");
    MethodReference m = MethodReference.findOrCreate(t, "<init>", "(Ljava/lang/Object;)V");
    Collection<IMethod> c = cha.getPossibleTargets(m);
    for (IMethod method : c) {
      System.err.println(method);
    }
    assertEquals(1, c.size());
  }

}
