			function rotate_x(center, sin_cos_angle, point)
			{
				var diff1 = point[1]-center[1];
				var diff2 = center[2]-point[2];

				point[1] = center[1]+diff1*sin_cos_angle[1]+diff2*sin_cos_angle[0];
				point[2] = center[2]-diff2*sin_cos_angle[1]+diff1*sin_cos_angle[0];
			}

			function rotate_x_normal(sin_cos_angle, point)
			{
				var temp = point[1];
				
				point[1] = temp*sin_cos_angle[1]-point[2]*sin_cos_angle[0];
				point[2] = point[2]*sin_cos_angle[1]+temp*sin_cos_angle[0];
			}

			function rotate_y(center, sin_cos_angle, point)
			{		
				var diff1 = point[0]-center[0];
				var diff2 = point[2]-center[2];

				point[0] = center[0]+diff1*sin_cos_angle[1]+diff2*sin_cos_angle[0];
				point[2] = center[2]+diff2*sin_cos_angle[1]-diff1*sin_cos_angle[0];
			}

			function rotate_y_normal(sin_cos_angle, point)
			{
				var temp = point[0];
				
				point[0] = temp*sin_cos_angle[1]+point[2]*sin_cos_angle[0];
				point[2] = point[2]*sin_cos_angle[1]-temp*sin_cos_angle[0];
			}

			function rotate_z(center, sin_cos_angle, point)
			{
				var diff1 = point[0]-center[0];
				var diff2 = point[1]-center[1];

				point[0] = center[0]+diff1*sin_cos_angle[1]-diff2*sin_cos_angle[0];
				point[1] = center[1]+diff2*sin_cos_angle[1]+diff1*sin_cos_angle[0];
			}
				
			function rotate_z_normal(sin_cos_angle, point)
			{
				var temp = point[0];
				
				point[0] = temp*sin_cos_angle[1]-point[1]*sin_cos_angle[0];
				point[1] = point[1]*sin_cos_angle[1]+temp*sin_cos_angle[0];
			}		

			
			function get_rotation_parameter(center, vector, teta)
			{
				var result = new Array();
				
				var u_u = vector[0]*vector[0];
				var v_v = vector[1]*vector[1];
				var w_w = vector[2]*vector[2]; 

				var v_v_p_w_w = (v_v+w_w);
				var u_u_p_w_w = (u_u+w_w);
				var u_u_p_v_v = (u_u+v_v);

				var b_v_p_c_w = center[1]*vector[1]+center[2]*vector[2];
				var a_u_p_c_w = center[0]*vector[0]+center[2]*vector[2];
				var a_u_p_b_v = center[0]*vector[0]+center[1]*vector[1];

				var b_w_m_c_v = center[1]*vector[2]-center[2]*vector[1];
				var c_u_m_a_w = center[2]*vector[0]-center[0]*vector[2];
				var a_v_m_b_u = center[0]*vector[1]-center[1]*vector[0];

				var den = v_v+u_u+w_w;

				result[0] = den;

				result[1] = v_v_p_w_w;
				result[2] = u_u_p_w_w;
				result[3] = u_u_p_v_v;

				result[4] = center[0]*v_v_p_w_w;
				result[5] = center[1]*u_u_p_w_w;
				result[6] = center[2]*u_u_p_v_v;

				result[7] = b_v_p_c_w;
				result[8] = a_u_p_c_w;
				result[9] = a_u_p_b_v;

				result[10] = Math.cos(teta);

				result[11] = Math.sin(teta)*Math.sqrt(den);

				result[12] = b_w_m_c_v;
				result[13] = c_u_m_a_w;
				result[14] = a_v_m_b_u;

				result[15] = center[0];
				result[16] = center[1];
				result[17] = center[2];
				result[18] = vector[0];
				result[19] = vector[1];
				result[20] = vector[2];

				
				return result;
			}

			
			function rotate(p, point)
			{
				var p_20_p_2 = p[20]*point[2];
				var p_19_p_1 = p[19]*point[1];
				var p_18_p_0 = p[18]*point[0];
				var u_x_p_v_y_p_w_z = p_18_p_0+p_19_p_1+p_20_p_2;
				
				var temp0 = point[0];
				var temp1 = point[1];

				point[0] = (p[4]+p[18]*(-p[7]+u_x_p_v_y_p_w_z)+((temp0-p[15])*p[1]+p[18]*(p[7]-p_19_p_1-p_20_p_2))*p[10]+p[11]*(p[12]-p[20]*temp1+p[19]*point[2]))/p[0];
				point[1] = (p[5]+p[19]*(-p[8]+u_x_p_v_y_p_w_z)+((temp1-p[16])*p[2]+p[19]*(p[8]-p_18_p_0-p_20_p_2))*p[10]+p[11]*(p[13]+p[20]*temp0-p[18]*point[2]))/p[0];
				point[2] = (p[6]+p[20]*(-p[9]+u_x_p_v_y_p_w_z)+((point[2]-p[17])*p[3]+p[20]*(p[9]-p_18_p_0-p_19_p_1))*p[10]+p[11]*(p[14]-p[19]*temp0+p[18]*temp1))/p[0];
			}

			function translate(vector, point)
			{
				point[0] = point[0] + vector[0];
				point[1] = point[1] + vector[1];
				point[2] = point[2] + vector[2];
			}

			function scale(vector, point)
			{
				point[0] = point[0] * vector[0];
				point[1] = point[1] * vector[1];
				point[2] = point[2] * vector[2];
			}
			
			
			function translate_solid(vector, solid)
			{
				translate(vector, solid.center);
				
				for (var i=0; i<solid.points_number; i++)
				{
					translate(vector, solid.points[i]);
				}
			}
			
			function translate_solid_direction(vector, delta, solid)
			{
				translate([vector[0]*delta, vector[1]*delta, vector[2]*delta], solid.center);
				
				for (var i=0; i<solid.points_number; i++)
				{
					translate([vector[0]*delta, vector[1]*delta, vector[2]*delta], solid.points[i]);
				}
			}

			function scale_solid(vector, solid)
			{
				var da = solid.center;
				var a = [-solid.center[0], -solid.center[1], -solid.center[2]];
					
				translate_solid(a, solid);
        for (var i=0; i<solid.points_number; i++)
				{
					scale(vector, solid.points[i]);
				}
				
        translate_solid(da, solid);
			}


			function rotate_solid(point, vector, angle, solid)
			{
				parametri = get_rotation_parameter(point, vector, angle);
				parametri2 = get_rotation_parameter([0, 0, 0], vector, angle);

				rotate(parametri, solid.center);
				rotate(parametri2, solid.axis_x);
				rotate(parametri2, solid.axis_y);
				rotate(parametri2, solid.axis_z);
				
				for (var i=0; i<solid.faces_number; i++)
				{
					rotate(parametri2, solid.normals[i]);
        }
					
				for (var j=0; j<solid.points_number; j++)
				{
					rotate(parametri, solid.points[j]);					
				}
			}

			function rotate_solid_fast(parametri1, parametri2, solid)
			{
				rotate(parametri1, solid.center);
				rotate(parametri2, solid.axis_x);
				rotate(parametri2, solid.axis_y);
				rotate(parametri2, solid.axis_z);
				
				for (var i=0; i<solid.faces_number; i++)
				{
					rotate(parametri2, solid.normals[i]);
        }
					
				for (var j=0; j<solid.points_number; j++)
				{
					rotate(parametri1, solid.points[j]);					
				}
			}

			function rotate_solid_x(center, angle, solid)
			{

				var sin_cosin_teta = [Math.sin(angle), Math.cos(angle)];

				rotate_x(center, sin_cosin_teta, solid.center);
				rotate_x_normal(sin_cosin_teta, solid.axis_x);
				rotate_x_normal(sin_cosin_teta, solid.axis_y);
				rotate_x_normal(sin_cosin_teta, solid.axis_z);
				
				for (var i=0; i<solid.faces_number; i++)
				{
					rotate_x_normal(sin_cosin_teta, solid.normals[i]);
        }
					
				for (var j=0; j<solid.points_number; j++)
				{
						rotate_x(center, sin_cosin_teta, solid.points[j]);					
				}
			}

			function rotate_solid_y(center, angle, solid)
			{
				var sin_cosin_teta = [Math.sin(angle), Math.cos(angle)];

				rotate_y(center, sin_cosin_teta, solid.center);
				rotate_y_normal(sin_cosin_teta, solid.axis_x);
				rotate_y_normal(sin_cosin_teta, solid.axis_y);
				rotate_y_normal(sin_cosin_teta, solid.axis_z);
				
				for (var i=0; i<solid.faces_number; i++)
				{
					rotate_y_normal(sin_cosin_teta, solid.normals[i]);
        }
					
				for (var j=0; j<solid.points_number; j++)
				{
					rotate_y(center, sin_cosin_teta, solid.points[j]);					
				}
			}

			function rotate_solid_z(center, angle, solid)
			{
				var sin_cosin_teta = [Math.sin(angle), Math.cos(angle)];

				rotate_z(center, sin_cosin_teta, solid.center);
				rotate_z_normal(sin_cosin_teta, solid.axis_x);
				rotate_z_normal(sin_cosin_teta, solid.axis_y);
				rotate_z_normal(sin_cosin_teta, solid.axis_z);
				
				for (var i=0; i<solid.faces_number; i++)
				{
					rotate_z_normal(sin_cosin_teta, solid.normals[i]);
        }
				
				for (var j=0; j<solid.points_number; j++)
				{
						rotate_z(center, sin_cosin_teta, solid.points[j]);					
				}
			}

			function project(distance, point)
			{
				var result = new Array();

				result[0] = point[0]*distance/point[2]+500;
				result[1] = 275-point[1]*distance/point[2];
				result[2] = distance;

				return result;
			}