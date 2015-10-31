// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int main() {

	int x;
	int y;
	int z;

	int a;

	if (x >= 0) {

		a = 0;
		a = a + 2;
		assert (a == 2);
		assert (!(x < 0));

		if (y >= 0) {
			a = a + 4;
			assert (a == 6);
			assert (!(x < 0) && !(y < 0));

			if (z >= 0) {
				a = a + 6;
				assert (a == 12);
				assert (!(x < 0) && !(y < 0) && !(z < 0));
			} else {
				a = a + 8;
				assert (a == 14);
				assert (!(x < 0) && !(y < 0) && !(z >= 0));
			}

		} else {

			a = a + 10;
			assert (a == 12);
			assert (!(x < 0) && !(y >= 0));

			if (z >= 0) {
				a = a + 12;
				assert (a == 24);
				assert (!(x < 0) && !(y >= 0) && !(z < 0));
			} else {
				a = a + 14;
				assert (a == 26);
				assert (!(x < 0) && !(y >= 0) && !(z >= 0));
			}

		}

		assert (a % 2 == 0 && x >= 0 && (y >= 0 || y < 0) && (z >= 0 || z < 0));

	} else {

		a = 1;
		a = a + 2;
		assert (a == 3);
		assert (!(x >= 0));

		if (y >= 0) {
			a = a + 4;
			assert (a == 7);
			assert (!(x >= 0) && !(y < 0));

			if (z >= 0) {
				a = a + 6;
				assert (a == 13);
				assert (!(x >= 0) && !(y < 0) && !(z < 0));
			} else {
				a = a + 8;
				assert (a == 15);
				assert (!(x >= 0) && !(y < 0) && !(z >= 0));
			}

		} else {

			a = a + 10;
			assert (a == 13);
			assert (!(x >= 0) && !(y >= 0));

			if (z >= 0) {
				a = a + 12;
				assert (a == 25);
				assert (!(x >= 0) && !(y >= 0) && !(z < 0));
			} else {
				a = a + 14;
				assert (a == 27);
				assert (!(x >= 0) && !(y >= 0) && !(z >= 0));
			}

		}

		assert (a % 2 == 1 && x < 0 && (y >= 0 || y < 0) && (z >= 0 || z < 0));

	}

	// Go over the top.
	int x1;
	int x2;
	int x3;
	int x4;
	int x5;

	if (x1 >= 0 && x2 >= 0) {
		if (x3 == 0) {
			if (x4 <= 0 && x5 >= 0) {
				assert (x1 / x3 == x1 && x2 / x3 == x2 && x3 / x3 == x3 - x3 && x4 / x3 == x4 && x5 / x3 == x5);
			} else {
				assert (x1 / x3 == x1 && x2 / x3 == x2 && x3 / x3 == x3 - x3 && x4 / x3 == x4 && x5 / x3 == x5);
			}
		} else {
			int x6; x6 = 666;
			int x7; x7 = 777;

			if (x6 % 2 == 0) {
				x6 = x6 - 1;
				x7 = x7 + 1;

				assert (x6 + x7 == (666 + 777) / (x3 - x3 + x1 - x1));
			} else {
				x6 = x6 - 2;
				x7 = x7 + 2;

				assert ((((x6 + x7 != 888))));
			}

			int m; int n; int p;

			if (m <= 0 && n == 0 && p >= 0) {
				if (1 || 0) {
					if (1) {
						if (!0 && !!!0) {
							assert (n / m == 0 && n / p == 0);
							assert (x6 == 665);

							x6 = x6 + 1;

							if (1) {
								x6 = x6;
								if (1) {
									x6 = x6;
									if (1) {
										x6 = x6;
										assert (x6 == 666);
									} else {
										assert (x6 == 666);
									}
								} else {
									assert (x6 == 666);
								}
							} else {
								assert (x6 == 666);
								assert (x6 == 666);

								x6 = x6 + x6 - x6;

								if (x6 == x6) {
									if (x6 == x6) {
										if (x6 == x6) {
											if (x6 == x6) {
												if (x6 == x6) {
													if (x6 == x6) {
														if (x6 == x6) {
															if (x6 == x6) {
																if (x6 == x6) {
																	x6 = x6 * (x6 - x6);

																	int d;
																	d = 2;
																	d = d + 1;
																	d = d + 2;
																	d = d * d;

																	if (5 * 5 == 25 && d == 25) {
																		assert d != d / d;
																		d = 0;
																		if (x6 == 0) {
																			assert x6 == x6 + x6 / x6 - x6;
																			assert d == d / d;
																		}

																		d = 3;
																		int e;

																		if (e % 3 == 0) {
																			assert ((d + e) % 3 == 0);
																		} else {
																			if (e % 3 == 1) {
																				assert ((d + e) % 3 == 1);
																			} else {
																				if (e % 3 == 2) {
																					assert ((d + e) % 3 == 2);
																				}
																			}
																		}

																		int f;

																		if (f == 0) {
																			int g;
																			g = 0;
																			if (e + f + g == 0) {
																				assert (e == 0 && f == 0 && g == 0);
																			}
																		} else {
																			int h;
																			h = -f;
																			if (e + f + h == 0) {
																				assert (e == 0 && (h + f == 0));
																			} else {
																				int w;
																				w = w;
																				assert (w == w);
																				w = w == w;
																				assert (w == 1);

																				if (a == 2) {
																					assert (a == 1 + 1);
																				} else {
																					if (a == 0) {
																						assert (0 == a / (0 + a));
																					} else {
																						assert (a + h == h + a);
																						assert (a != 2 && a != 0);
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

								assert (x6 == 0 + 0 + 0 + 0 + 0 + 0 + 0 + x6);
							}
						}
					}
				}
			} else {
				assert 1;
			}
		}
	}

	return 0;

}