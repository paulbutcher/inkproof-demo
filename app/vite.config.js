// Copyright (c) 2026 Paul Butcher. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.
import lasm from '@lasm/cli/vite';
export default { root: 'web', plugins: [lasm()], build: { outDir: '../dist', emptyOutDir: true }, server: { fs: { allow: ['..', '../..'] } } };
