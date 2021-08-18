/*
 * Copyright (c) 2006 IBM Corporation.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     IBM Corporation - initial API and implementation
 */
package reflection;

import java.lang.reflect.InvocationTargetException;

public class Reflect1 {

  public static void main(String[] args)
      throws ClassNotFoundException, InstantiationException, IllegalAccessException, IllegalArgumentException, InvocationTargetException, NoSuchMethodException, SecurityException {
    Class<?> c = Class.forName("java.lang.Integer");
    Integer i = (Integer) c.getDeclaredConstructor(int.class).newInstance(5);
    System.err.println(i);
  }
}